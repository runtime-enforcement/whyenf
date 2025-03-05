(lang dune 3.13)

(name lifeboat)

(generate_opam_files true)

(source
 (github runtime-enforcement/whyenf))

(authors
 "François Hublet <fhublet@ethz.ch>"
 "Leonardo Lima <leonardo@di.ku.dk>"
 "David Basin <basin@inf.ethz.ch>"
 "Srđan Krstić <srdan.krstic@inf.ethz.ch>"
 "Dmitriy Traytel <traytel@di.ku.dk>")

(maintainers
 "François Hublet <fhublet@ethz.ch>"
 "Leonardo Lima <leonardo@di.ku.dk>")

(license LICENSE)

(documentation https://url/to/documentation)

(using menhir 3.0)

(package
 (name lifeboat)
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
  (z3 (>= 4.13.0)))
 (tags
  (proactive runtime enforcement)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
