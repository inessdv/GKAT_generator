(lang dune 3.10)

(name KA_equiv)

(generate_opam_files false)

(source
 (github inessdv/UR2Phd_KAT))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name KA_equiv)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends (ocaml (>= 5.1)) dune unionFind hashcons z3 qcheck (ounit2 :with-test))
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
