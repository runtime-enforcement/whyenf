# WhyMon: explanations as verdicts

## Getting Started

To execute the project on your local machine, follow the instructions below.

### Prerequisites

We recommend that you install a recent verion of the OCaml compiler (>= 4.11) and necessary dependencies with [opam](https://opam.ocaml.org/doc/Install.html).

In particular, if you are a Debian/Ubuntu user

```
# apt-get install opam
$ opam switch 4.13.1
$ eval $(opam config env)
$ opam install dune core_kernel base zarith menhir
```

or if you are an Arch Linux user

```
# pacman -S opam
$ opam switch 4.13.1
$ eval $(opam config env)
$ opam install dune core_kernel base zarith menhir
```

should be enough.

### Running

From the root folder, you can compile the code with

```
$ dune build
```

to obtain the executable **whymon.exe** inside the folder [bin](bin/). Moreover,

```
$ ./bin/whymon.exe --help
```

will print the usage statement. For instance, you can run one of our predefined examples with our output checker:

```
$ ./bin/whymon.exe -mode verified -sig examples/paper/publish_approve_manager.sig -formula examples/paper/publish_approve_manager.mfotl -log examples/paper/publish_approve_manager.log
```

You can remove the binary and clean the working directory with

```
$ dune clean
```

### Formalization

The file [src/checker.ml](src/checker.ml) corresponds to the code extracted from the Isabelle formalization.

You can also extract this code on your local machine.

The formalization is compatible with [Isabelle 2022](https://isabelle.in.tum.de/website-Isabelle2022/), and depends on the corresponding [Archive of Formal Proofs (AFP) version](https://foss.heptapod.net/isa-afp/afp-devel/-/tree/Isabelle2022).

After setting up the AFP locally (by following [these](https://www.isa-afp.org/help/) instructions), you can run

```
$ isabelle build -vd thys -eD code
```

from inside the [formalization](formalization/) folder to produce the file `formalization/code/checker.ocaml`.

### Syntax

### Metric First-Order Temporal Logic
```
{PRED} ::= string

{VAR} ::= string

{VARS} ::=   {VAR}
           | {VAR}, {VARS}

{CONST} ::= quoted string

{I}  ::= [{NAT}, {UPPERBOUND}]

{UPPERBOUND} ::=   {NAT}
                 | INFINITY   (∞)

{f} ::=   {PRED}({VARS})
        | true                  (⊤)
        | false                 (⊥)
        | {VAR} EQCONST {CONST} (=)
        | NOT {f}               (¬)
        | {f} AND {f}           (∧)
        | {f} OR  {f}           (∨)
        | {f} IMPLIES {f}       (→)
        | {f} IFF {f}           (↔)
        | EXISTS {VAR}. {f}     (∃)
        | FORALL {VAR}. {f}     {∀}
        | PREV{I} {f}           (●)
        | NEXT{I} {f}           (○)
        | ONCE{I} {f}           (⧫)
        | EVENTUALLY{I} {f}     (◊)
        | HISTORICALLY{I} {f}   (■)
        | ALWAYS{I} {f}         (□)
        | {f} SINCE{I} {f}      (S)
        | {f} UNTIL{I} {f}      (U)
        | {f} TRIGGER{I} {f}    (T)
        | {f} RELEASE{I} {f}    (R)
```

Note that this tool also supports the equivalent Unicode characters (on the right).

### Signature
```
{TYPE} ::= string | int

{VARTYPES} ::=   {VAR}:{TYPE}
               | {VAR}:{TYPE}, {VARTYPES}

{SIG} ::=   {PRED}({VARTYPES})
          | {PRED}({VARTYPES}) \n {SIG}
```

### Trace
```
{VALUES} ::=   string
             | string, {VALUES}

{TRACE} :=   @{NAT} {PREDICATE}(VALUES)*
           | @{NAT} {PREDICATE}()* \n {TRACE}
```

## License

This project is licensed under the GNU Lesser GPL-3.0 license - see [LICENSE](LICENSE) for details.
