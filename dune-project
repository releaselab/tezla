(lang dune 2.03)
(name tezla)

(generate_opam_files true)

(source (uri "git+https://gitlab.com/releaselab/fresco/michelscil.git"))
(bug_reports "https://gitlab.com/releaselab/fresco/michelscil/issues")
(homepage "https://gitlab.com/releaselab/fresco/michelscil")
(license MIT)
(authors "João Santos Reis <joaosreis@outlook.pt>")
(maintainers "João Santos Reis <joaosreis@outlook.pt>")

(package
 (name tezla)
 (synopsis "An instantiation of SCIL for the Michelson language")
 (depends
  (dune :build)
  (zarith :build)
  (cmdliner :with-test)
  (alcotest :with-test)
  (bisect_ppx (and :dev (>= 2.0.0)))))

