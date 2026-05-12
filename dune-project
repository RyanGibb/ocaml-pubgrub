(lang dune 3.18)

(generate_opam_files)

(name pubgrub)

(license MIT)

(maintainers "Ryan Gibb <ryan@freumh.org>")

(package
 (name pubgrub)
 (synopsis "PubGrub version solving algorithm")
 (depends
  (ocaml (>= 4.14))
  (ppx_expect :with-test)))
