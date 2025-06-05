# EnfGuard: a proactive real-time first-order enforcer

## Authors

The EnfGuard enforcer is the successor of the WhyEnf enforcer, which itself shares part of its
code base with the WhyMon monitoring tool.

The following individuals have contributed to the development of EnfGuard, WhyEnf, and/or WhyMon:

* François Hublet (ETH Zürich): EnfGuard (lead), WhyEnf (co-lead)
* Leonardo Lima (University of Copenhagen): EnfGuard, WhyEnf (co-lead), WhyMon (lead)
* Srđan Krstić (ETH Zürich): EnfGuard, WhyEnf
* Dmitriy Traytel (University of Copenhagen): EnfGuard, WhyEnf, WhyMon
* David Basin (ETH Zürich): EnfGuard, WhyEnf

## Getting Started

To execute the project on your local machine, follow the instructions below.

### Prerequisites

We recommend that you install a recent verion of the OCaml compiler (>= 4.11) and necessary dependencies with [opam](https://opam.ocaml.org/doc/Install.html).

In particular, if you are a Debian/Ubuntu user

```
# apt-get install opam libgmp-dev
```

and then

```
$ opam init -y
$ opam switch create 4.13.1
$ eval $(opam env --switch=4.13.1)
$ opam install dune core_kernel base zarith menhir js_of_ocaml js_of_ocaml-ppx \
               zarith_stubs_js dune-build-info qcheck pyml calendar
```

should be enough.

### Running

From the root folder, you can compile the code with

```
$ dune build
```

to obtain the executable **enfguard.exe** inside the folder [bin](bin/). Moreover, you can run one of our predefined examples with

```
$ ./bin/enfguard.exe -sig examples/enforcement/paper/case_study/arfelt.sig -formula examples/enforcement/paper/case_study/formulae_whyenf/arfelt_2_limitation.mfotl -log examples/enforcement/paper/case_study/arfelt.log
```

You can remove the binary and clean the working directory with

```
$ dune clean
```

## License

This project and its predecessors WhyEnf and WhyMon are licensed under the GNU Lesser GPL-3.0 license - see [LICENSE](LICENSE) for details.
