(lang dune 3.0)

(name whyenf)

(generate_opam_files true)

(source
 (github runtime-enforcement/whyenf))

(authors
 "François Hublet <fhublet@ethz.ch>"
 "Leonardo Lima <hi@nameless.computer>")

(maintainers
 "François Hublet <fhublet@ethz.ch>"
 "Leonardo Lima <hi@nameless.computer>")

(license LICENSE)

(documentation https://url/to/documentation)

(using menhir 2.0)

(package
 (name whyenf)
 (synopsis "")
 (description "")
 (depends
  (ocaml (>= 4.11))
  (dune (>= 3.0))
  (core_kernel (>= v0.14))
  (base (>= v0.14))
  (menhir (>= 20220210))
  (zarith (>= 1.11))
  (zarith_stubs_js (>= v0.14.1)))
 (tags
  (proactive runtime enforcement)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
