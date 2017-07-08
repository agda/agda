Add support for a new version of GHC (in the stable branch)
===========================================================

Let's suppose the new version of GHC is X.Y.Z.

* Install the tools in the `build-tools` field(s) of Agda.cabal.

* Update Cabal index:

  `cabal update`

* Install Agda dependencies:

  `cabal install --enable-test --only-dependencies`

* Install Agda using GHC X.Y.Z:

  `make install-bin`

* Run the test-suite:

  `make test`

* Test the different flags for installing Agda describes in Agda.cabal.

* Ensure that cabal haddock works:

  `make haddock`

* Test the fix-agda-whitespace program:

  `make build-fix-agda-whitespace`

* Test the hTags program:

  `make TAGS`

* Test the size-solver program:

  ```bash
  make install-size-solver
  make test-size-solver
  ```

* Test the agda-bisect program:

  `make install-agda-bisect`

* Update the `tested-with` field in Agda.cabal, agda-bisect,
  fix-agda-whitespace.cabal, hTags.cabal and std-lib/lib.agda.

* Update the CHANGELOG files (Agda and the standard library):


   ```
   Installation and infrastructure
   -------------------------------

   * Added support for GHC X.Y.Z.
   ```

* Travis: Add an instance for GHC X.Y.Z to .travis.yml.

* Record your changes in the stable branch.

* Merge the stable branch into the master.

* Push the stable and master branches.
