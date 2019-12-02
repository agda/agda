Add support for a new version of GHC (in the stable branch)
===========================================================

Let's suppose the new version of GHC is X.Y.Z.

* Update Cabal index:

  `cabal update`

* Install the tools in the `build-tools` field(s) of Agda.cabal.

* Install Agda dependencies:

  `cabal install --enable-test --only-dependencies`

* Install Agda using GHC X.Y.Z:

  `make install-bin`

* Test the fix-agda-whitespace program:

  `make build-fix-agda-whitespace`

* Run the test-suite:

  `make test`

* Test the different flags for installing Agda describes in Agda.cabal.

* Ensure that cabal haddock works:

  `make haddock`

* Test the hTags program:

  `make TAGS`

* Test the size-solver program:

  ```bash
  make install-size-solver
  cabal install shelltestrunner
  make test-size-solver
  ```

* Test the agda-bisect program:

  `make install-agda-bisect`

* Test the `closed-issues-for-milestone` program.

* Update the `tested-with` field in .cabal files.

  If GHC X.Y.Z is a bug-fix release run

    ./src/release-tools/change-tested-with-field.bash X.Y.(Z-1) X.Y.Z

  else update manually the field.

* Update the `tested-with` field in std-lib/lib.agda.

* Update the CHANGELOG files (Agda and the standard library):


   ```
   Installation and infrastructure
   -------------------------------

   * Added support for GHC X.Y.Z.
   ```

* Travis:

  - Add an instance for GHC X.Y.Z.

  - Update Haddock test for using GHC X.Y.Z.

* STACKAGE:

  - Create `stack-X.Y.Z.yaml` using as resolver `ghc-X.Y.Z`.

  - Test the build using `stack-X.Y.Z.yaml`.

  - Add `stack-X.Y.Z.yaml` to the `extra-source-files` field in
    Agda.cabal.

  - Add an instance using `stack-X.Y.Z.yaml` to Travis.

* User manual: Update the tested versions of GHC in
  `/doc/user-manual/getting-started/prerequisites.rst`.

* Add the file `.ghciXY` and modify the `.ghci`.

* Record your changes in the stable branch.

* Merge the stable branch into the master.

* Push the stable and master branches.
