(lang dune 3.13)

(name enfflash)

(generate_opam_files true)

(source
 (github runtime-enforcement/enfflash))

(authors
 "François Hublet <fhublet@ethz.ch>"
 "David Basin <basin@inf.ethz.ch>"
 "Srđan Krstić <srdan.krstic@inf.ethz.ch>")

(maintainers
 "François Hublet <fhublet@ethz.ch>")

(license LICENSE)

(documentation https://url/to/documentation)

(using menhir 3.0)

(package
 (name enfflash)
 (synopsis "")
 (description "Proactive Runtime Enforcement")
 (depends
  (ocaml (>= 4.11))
  (dune (>= 3.0))
  (core_kernel (>= v0.14))
  (base (>= v0.14))
  (menhir (>= 20220210))
  (zarith (>= 1.11))
  (zarith_stubs_js (>= v0.14.1))
  (z3 (>= 4.13.0))
  (calendar (>= 3.0.0))
  (pyml (>= 20250807))
  (core_unix (>= v0.15.2)))
 (tags
  (proactive runtime enforcement)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
