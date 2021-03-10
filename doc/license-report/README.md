Agda dependencies license report
================================

The [Makefile](Makefile) here helps you to generate a listing of the
licenses of the Agda dependencies using `cabal-plan`.

It prints the declared licence of every Cabal package that the Agda
binary depends on (as determined by the configuration in the Cabal
build directory `dist-newstyle`).
Note that the binary may depend on non-Cabal packages as well.

The license for the `rts` package is that of (some version of)
the `ghc` package.

Instructions
------------

1. If you are lacking one of the prerequisites `cabal-plan` or `pandoc`
   (details see [Makefile](Makefile)),
   run `make install` here.

2. Run `make` here.

3. Result is in `index.html`.

Note
----

If you do not have a cabal build plan for Agda yet, i.e., a file
`dist-newstyle/cache/plan.json`, the `make` step will run `cabal v2-configure`
in the root folder with flags to get the maximal dependencies, like
```
cabal v2-configure --enable-tests -fenable-cluster-counting
```
(details see [Makefile](Makefile)).

However, there is no check that the build plan is up-to-date nor includes the maximal dependencies.
You can force it by:
```
make -B configure
```
