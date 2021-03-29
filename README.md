# Explanator2: Judgement Day

The Explanator2 is a tool for online monitoring satisfaction/violation explanations of MTL (Metric Temporal Logic) and MDL (Metric Dynamic Logic) formulas on arbitrary words. 

It is built upon the [Explanator](https://bitbucket.org/traytel/explanator/src/master/), a previous work by [Bhargav Bhatt](https://bhargavbh.github.io/) and [Dmitriy Traytel](https://www21.in.tum.de/~traytel/).

## Getting Started

These are the basic steps to take if you want to run the project on your local machine.

### Prerequisites

Explanator2 depends on a recent (>= 4.04.0) version of the OCaml compiler.

We recommend that you install the OCaml compiler and necessary libraries with [OPAM](https://opam.ocaml.org/doc/Install.html), the OCaml package manager.

In particular, if you are a Ubuntu/Debian user

```
# apt-get install opam
$ opam switch 4.11.1
$ eval $(opam config env)
$ opam install safa menhir
```

or if you are an Arch Linux user

```
# pacman -S opam
$ opam switch 4.11.1
$ eval $(opam config env)
$ opam install safa menhir
```

should be enough.

### Running

Inside [src/](src/) there is a **Makefile**. You can compile the code with

```
$ make
```

to obtain a binary **explanator2.native**, and

```
$ ./explanator2.native
```

to run an example. When finished,

```
$ make clean
```

will remove the binary and clean the working directory.

### Usage

```
$ ./explanator2.native -?
```

provides information about the tool's user interface.

## License

This project is licensed under the GNU Lesser GPL-3.0 license - see [LICENSE](LICENSE) for details.