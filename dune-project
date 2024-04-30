(lang dune 3.8)
(using coq 0.8)
(name coq-ogs)

(license "GPLv3")
(authors "REDACTED")
(maintainers "REDACTED")

(generate_opam_files true)

(package
 (name coq-ogs)
 (synopsis "An abstract, certified account of operational game semantics")
 (version 0.1)
 (depends
  (coq (= 8.17.1))
  (coq-coinduction (= 1.6))
  (coq-equations (= 1.3+8.17))
 )
)
