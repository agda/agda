Agda dependencies license report
================================

Using `cabal-plan`, you can generate a listing of the licenses of the Agda dependencies in this directory.
See [Makefile](Makefile) for prerequisites (`cabal-plan`, `pandoc`).

Instructions:

- Run `cabal v2-configure` in the root folder (to generate `dist-newstyle/`).
  This step can be skipped if you already have that folder,
  e.g., if you have run `cabal v2-build` or similar before.

- Run `make` here.

- Result is in `index.html`.
