(lang dune 3.0)

(name whymon)

(generate_opam_files true)

(source
 (github runtime-monitoring/whymon))

(authors "Leonardo Lima")

(maintainers "Leonardo Lima")

(license LICENSE)

(documentation https://url/to/documentation)

(using menhir 2.0)

(package
 (name whymon)
 (synopsis "")
 (description "")
 (depends
  (ocaml (>= 4.11))
  (dune (>= 3.0))
  (core_kernel (>= v0.14))
  (base (>= v0.14))
  (menhir (>= 20220210))
  (zarith (>= 1.11))
  (zarith_stubs_js (>= v0.14.1))
  (z3 (>= 4.12.2)))
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
