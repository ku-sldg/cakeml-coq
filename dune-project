(lang dune 3.16)
(using coq 0.8)

(name cakeml-semantics)
(version 0.1)

(generate_opam_files true)

(package
 (name cakeml-semantics)
 (depends
   coq-equations
   coq
   dune)
 (synopsis "CakeML semantic definitions")
 (description  "CakeML Definitions defined in Coq originally written to define a Gallina to CakeML translator.")
 (maintainers   "tjbarclay@ku.edu")
 (authors      "TJ Barclay")
)
