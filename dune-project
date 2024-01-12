(lang dune 3.8)
(using coq 0.8)
(name coq-ogs)

(license "GPLv3")
(authors "Peio Borthelle" "Tom Hirschowitz" "Guilhem Jaber" "Yannick Zakowski")
(maintainers "Peio Borthelle")
(source (gitlab yzakowsk/ogs-coq))
(bug_reports "https://gitlab.inria.fr/yzakowsk/ogs-coq/-/issues")

(generate_opam_files true)

(package
 (name coq-ogs)
 (synopsis "An abstract, certified account of operational game semantics.")
 (version 0.1)
 (depends
  (coq (= 8.17))
  (coq-coinduction (= 1.6))
  (coq-equations (= 1.3))
 )
)
