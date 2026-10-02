<p align="center">
  <img src="enfflash.png" alt="EnfFlash" width="520">
</p>

<p align="center">
  Fast runtime enforcement of first-order temporal policies.
</p>

---

EnfFlash sits between a system and its actions. It checks each event against a policy
written in Metric First-Order Temporal Logic (MFOTL), and, when needed, it

- **suppresses** an action that would violate the policy (e.g., using data after consent was revoked), or
- **causes** an action that the policy requires (e.g., deleting data within 30 days of a request).

Policies can refer to data values, to the past and the future, and to time windows. EnfFlash
compiles them into small imperative programs, so a decision typically takes well under a
millisecond, even with long histories.

## Install

On Linux or macOS:

```sh
./install.sh
```

The script installs what is missing (Rust via [rustup](https://rustup.rs/), OCaml via
[opam](https://opam.ocaml.org/), and the OCaml libraries in `enfflash.opam`) and builds
`bin/enfflash.exe`. It uses your current opam switch, or creates one with OCaml 4.13.1.
The first run takes a while, mostly to build the Z3 library. Afterwards, rebuild with `make`.

## Quick start

A policy has two files: a **signature** declaring the events, and a **formula**.

`examples/quickstart/consent.sig`: data may be used only with consent. The `-` marks `use`
as an event EnfFlash may suppress.

```
consent(user:string, purpose:string)
revoke(user:string, purpose:string)
use(purpose:string, data:string, user:string)-
```

`examples/quickstart/consent.mfotl`: whenever data is used for a purpose, the user has
consented to it and not revoked it since.

```
ALWAYS (FORALL p, d, u. use(p, d, u) IMPLIES (NOT revoke(u, p)) SINCE consent(u, p))
```

Events arrive as a log, one time-point per line (`@timestamp event; …`):

```
@0 consent("alice", "ads");
@5 use("ads", "d1", "alice");
@10 revoke("alice", "ads");
@12 use("ads", "d2", "alice");
```

```sh
$ ./bin/enfflash.exe -sig examples/quickstart/consent.sig \
                     -formula examples/quickstart/consent.mfotl \
                     -log examples/quickstart/consent.log
[Enforcer] @5 OK.
[Enforcer] @10 OK.
[Enforcer] @12 reactively commands:
Suppress:
use("ads", "d2", "alice")
```

Obligations work the same way. In `examples/quickstart/erasure.*`, `delete` is marked `+`
(EnfFlash may cause it), and every deletion request must be honored within 30 time units:

```
ALWAYS (FORALL u, d. deletion_request(u, d) IMPLIES EVENTUALLY[0,30] delete(u, d))
```

```sh
$ ./bin/enfflash.exe -sig examples/quickstart/erasure.sig \
                     -formula examples/quickstart/erasure.mfotl \
                     -log examples/quickstart/erasure.log
[Enforcer] @30 proactively commands:
Cause:
delete("alice", "d1")
```

(Output abridged: EnfFlash also reports the time-points where nothing happens.)

## Writing policies

**Signatures.** One event per line, with typed arguments (`int`, `float`, `string`). A
suffix says what EnfFlash may do with the event: `-` suppress it, `+` cause it, none of
the two: only observe it.

**Formulas.** The main operators:

| | |
|---|---|
| `NOT`, `AND`, `OR`, `IMPLIES`, `IFF` | Boolean connectives |
| `FORALL x.`, `EXISTS x.` | quantifiers over event arguments |
| `ALWAYS φ` | φ holds at every time-point |
| `ONCE[a,b] φ`, `φ SINCE[a,b] ψ`, `PREV φ` | past: φ held between *a* and *b* time units ago, … |
| `EVENTUALLY[a,b] φ`, `NEXT φ` | future: φ must hold within [*a*, *b*] |
| `y <- SUM(x; g; φ)` (also `CNT`, `AVG`, `MIN`, `MAX`, `MED`) | aggregation over the satisfying values of φ, grouped by `g` |
| `LET p(x) = φ IN ψ` | named sub-formula |

Intervals are optional (`ONCE φ` means "at some point in the past") and may be unbounded
(`[0,*)`). `examples/tests/` contains over 70 small policies with their expected output.

**Functions.** Formulas can call the built-in arithmetic and comparison operators
(`+`, `-`, `*`, `/`, `=`, `<`, `^` for string concatenation, …) and your own functions,
written in Python. Declare each function in the signature with its argument and result
types, define it in a Python file, and pass the file with `-func`:

```
# examples/quickstart/access.sig          # examples/quickstart/access.py
grant(user:string, area:string)           def area(path):
access(user:string, path:string)-             # "/admin/users" -> "admin"
fun area(path:string): string                 return path.split("/")[1]
```

```
ALWAYS (FORALL u, p. access(u, p) IMPLIES (EXISTS a. a = area(p) AND ONCE grant(u, a)))
```

```sh
$ ./bin/enfflash.exe -sig examples/quickstart/access.sig \
                     -formula examples/quickstart/access.mfotl \
                     -func examples/quickstart/access.py \
                     -log examples/quickstart/access.log
[Enforcer] @2 reactively commands:
Suppress:
access("alice", "/billing/invoices")
```

A function's arguments must be known when it is called: bind them through events (here,
`p` comes from `access`), and name its result with `=`, as `a` above. Three kinds of
declarations exist:

| | |
|---|---|
| `fun f(x:int): int` | a function |
| `sfun f(x:int): int` | a *stable* function: applying it repeatedly yields finitely many values. Only stable functions may feed an event back into itself, e.g. `D(x) IMPLIES D(f(x))`; otherwise enforcement might not terminate |
| `afun f(k:int, v:int): (int, int)` | an aggregation: receives the list of tuples satisfying a formula and returns a list of tuples, as in `[k, l] <- f([k, v];; φ)` (see `examples/tests/grubbs.*`) |

Not every formula is enforceable: EnfFlash rejects a policy if it cannot guarantee to
enforce it by suppressing `-` events and causing `+` events, and explains why.

## Using EnfFlash in an application

Run EnfFlash as a long-lived process: write each time-point to its standard input as it
happens, and read its decision before letting the action proceed.

| Option | |
|---|---|
| `-json` | one JSON object per time-point, with the events to suppress or cause |
| `-state FILE` | save the enforcer's state on exit and restore it on start |
| `-func FILE` | Python file defining functions used in the formula |
| `-log FILE` | read events from a file instead of standard input |
| `-label` | report which rule triggered each action |
| `-no-run -output FILE` | only compile the policy to an `.ef` program |
| `-complexity` | print the estimated cost per time-point and exit |

Run `./bin/enfflash.exe -help` for all options.
[Instrlib](https://doi.org/10.1007/978-3-032-05435-7_10) instruments Python web applications
with EnfFlash as their enforcement backend.

## Repository

| | |
|---|---|
| `src/`, `bin/` | MFOTL-to-EF compiler (OCaml) |
| `enfflash/` | EF enforcement engine (Rust) |
| `lean/` | Lean 4 formalization of the compilation and its correctness ([lean/README.md](lean/README.md)) |
| `eval/paper/` | scripts that regenerate the paper's tables and figures ([eval/paper/README.md](eval/paper/README.md)) |
| `eval/enforcement/` | benchmark suite and the competing tools ([eval/enforcement/README.md](eval/enforcement/README.md)) |
| `eval/agent_banking/` | case study: security policies for an LLM banking agent (AgentDojo) |
| `examples/tests/`, `tests/` | regression tests (`make test`) |

## License

GNU Lesser General Public License v3.0, as EnfGuard, WhyEnf, and WhyMon, from which it borrows some of its (OCaml) code base. See [LICENSE](LICENSE).

## Citing

If you use EnfFlash in your research, please cite:

```bibtex
@misc{EnfFlash,
  title  = {Practical Runtime Enforcement of First-Order Temporal Requirements},
  author = {Hublet, Fran{\c{c}}ois and Krsti{\'c}, Sr{\dj}an and Basin, David},
  year   = {2026},
  note   = {Under review}
}
```