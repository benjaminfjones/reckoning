(lang dune 3.6)

(name reckoning)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Benjamin F Jones")

(maintainers "Benjamin F Jones")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name reckoning)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml dune ppx_inline_test)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
