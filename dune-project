(lang dune 3.8)
(using coq 0.8)

(name cakeml-semantics)
(version 0.1)

(generate_opam_files true)

(package
 (name cakeml-semantics)
 (depends
  (coq-equations (>= 1.3+8.15))
  (coq (>= 8.15.1)))
 (synopsis "CakeML semantic definitions")
 (description  "")
 (maintainers   "tjbarclay@ku.edu")
 (authors      "TJ Barclay")
)
