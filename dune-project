(lang dune 3.0)

(name explanator2)

(generate_opam_files true)

(source
 (github runtime-monitoring/explanator2))

(authors "Leonardo Lima")

(maintainers "Leonardo Lima")

(license LICENSE)

(documentation https://url/to/documentation)

(using menhir 2.0)

(package
 (name explanator2)
 (synopsis "Explanator2 is a tool for online monitoring satisfaction and violation explanations of MTL (Metric Temporal Logic) formulas on arbitrary words")
 (description "")
 (depends
  (ocaml (>= 4.11))
  (dune (>= 3.0))
  (core_kernel (>= v0.14))
  (base (>= v0.14))
  (zarith (>= 1.11))
  (menhir (>= 20220210)))
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
