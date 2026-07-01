# Enfflash: a proactive real-time first-order enforcer

## Authors

Enfflash is the successor of EnfGuard and WhyEnf, which themselves share part of their
code base with the WhyMon monitoring tool.

The following individuals have contributed to the development of Enfflash, EnfGuard, WhyEnf, and/or WhyMon:

* François Hublet (ETH Zürich): Enfflash (lead), EnfGuard (lead), WhyEnf (co-lead)
* Leonardo Lima (University of Copenhagen): EnfGuard, WhyEnf (co-lead), WhyMon (lead)
* Srđan Krstić (ETH Zürich): Enfflash, EnfGuard, WhyEnf
* Dmitriy Traytel (University of Copenhagen): EnfGuard, WhyEnf, WhyMon
* David Basin (ETH Zürich): Enfflash, EnfGuard, WhyEnf

## Getting Started

To execute the project on your local machine, follow the instructions below.

### Prerequisites

Enfflash uses a two-stage architecture: the OCaml frontend compiles an MFOTL policy to an
intermediate `.ef` program, which is then executed by a Rust enforcement engine.

**OCaml frontend** — we recommend a recent version of the OCaml compiler (>= 4.11) and
necessary dependencies via [opam](https://opam.ocaml.org/doc/Install.html).

On Debian/Ubuntu:

```
# apt-get install opam libgmp-dev
```

then:

```
$ opam init -y
$ opam switch create 4.13.1
$ eval $(opam env --switch=4.13.1)
$ opam install dune core_kernel core_unix base zarith menhir \
               zarith_stubs_js dune-build-info qcheck pyml calendar str z3
```

**Rust engine** — install [rustup](https://rustup.rs/) and ensure the stable toolchain is active:

```
$ curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
$ rustup toolchain install stable
```

### Building

Build the OCaml frontend with:

```
$ dune build
```

Build the Rust enforcement engine with:

```
$ cargo build --release --manifest-path enfflash/Cargo.toml
```

### Running

The main entry point is the `enfflash` binary (OCaml frontend). It compiles the given MFOTL
policy and immediately passes control to the Rust `enfflash` engine:

```
$ ./enfflash -sig <sig-file> -formula <formula-file>
```

For example:

```
$ ./enfflash -sig examples/case_study/edg-gdpr/gdpr.sig \
             -formula examples/case_study/edg-gdpr/gdpr.mfotl
```

Log events are read from stdin by default; pass `-log <file>` to read from a file instead.

#### Selected flags

| Flag | Description |
|------|-------------|
| `-sig FILE` | Signature file |
| `-formula FILE` | MFOTL formula file |
| `-log FILE` | Log file (reads stdin if omitted) |
| `-func FILE` | Python file with user-defined function definitions |
| `-output FILE` | Write compiled `.ef` program to FILE instead of a temp file |
| `-no-run` | Compile only; do not launch the enforcer |
| `-complexity` | Print estimated per-time-point complexity and exit |
| `-parallel` | Split the policy and run one enforcer per clause group in parallel |
| `-json` | Output enforcement actions in JSON format |
| `-label` | Print rule labels in enforcement output |
| `-verbose N` | Verbosity level (0 = off, 1 = basic, 2 = full) |
| `-state FILE` | Save/restore enforcer state to/from FILE |

#### Parallel mode

For large policies, the `-parallel` flag compiles the policy into independent clause groups
and runs one `enfflash` instance per group:

```
$ ./enfflash -sig <sig> -formula <formula> -parallel [-num-groups K] [-filtered]
```

### Cleaning up

```
$ dune clean
```

## Evaluation

Reproduction instructions for the empirical benchmarks (gdpr, fun, cluster, agg, ic, nokia),
including installation of the comparison tools (MonPoly/Enfpoly, EnfGuard, WhyEnf), are in
[eval/enforcement/README.md](eval/enforcement/README.md).

## License

This project and its predecessors EnfGuard, WhyEnf, and WhyMon are licensed under the
GNU Lesser GPL-3.0 license — see [LICENSE](LICENSE) for details.
