# Explanator2: Judgement Day

The Explanator2 is a tool for online monitoring satisfaction and violation explanations of MTL (Metric Temporal Logic) formulas on an arbitrary trace.

It is the successor of the [Explanator](https://bitbucket.org/traytel/explanator/src/master/), a previous work by [Bhargav Bhatt](https://bhargavbh.github.io/) and [Dmitriy Traytel](https://www21.in.tum.de/~traytel/).

## Getting Started

These are the basic steps to take if you want to run the project on your local machine.

### Prerequisites

The Explanator2 depends on a recent (>= 4.04.0) version of the OCaml compiler.

We recommend that you install the OCaml compiler and necessary libraries with [OPAM](https://opam.ocaml.org/doc/Install.html), the OCaml package manager.

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

You can compile the code with

```
$ dune build
```

to obtain a binary **explanator2.exe** inside [bin/](bin/), and

```
$ ./bin/explanator2.exe --help
```

to check the usage statement. When finished,

```
$ dune clean
```

will remove the binary and clean the working directory.

### Formalization

File [src/checker.ml](src/checker.ml) corresponds to the code extracted from the Isabelle formalization.

Alternatively, you can extract the code on your local machine using the command:

```
$ isabelle build -vd thys -eD code
```

from inside the [formalization/](formalization/) folder.

### Syntax

#### Metric Temporal Logic
```
{f} ::=   true
        | false
        | {ATOM}
        | NOT {f}
        | {f} AND {f}
        | {f} OR  {f}
        | {f} IFF {f}
        | {f} IMPLIES {f}
        | PREV{i} {f}
        | NEXT{i} {f}
        | ONCE{i} {f}
        | EVENTUALLY{i} {f}
        | HISTORICALLY{i} {f}
        | ALWAYS{i} {f}
        | {f} SINCE{i} {f}
        | {f} UNTIL{i} {f}
        | {f} TRIGGER{i} {f}
        | {f} RELEASE{i} {f}

{i}  ::= [{NAT}, {UPPERBOUND}]
{UPPERBOUND} ::= {NAT} | INFINITY
```

#### Log
```
{LOG} :=   @{NAT} {ATOM}*
         | @{NAT} {ATOM}* \n {LOG}
```

## License

This project is licensed under the GNU Lesser GPL-3.0 license - see [LICENSE](LICENSE) for details.
