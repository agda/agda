Testing the repository with a new version of GHC
-------

Let's suppose the new version of GHC is X.Y.Z and the current
maintenance branch is maint-2.4.0.

* Create a new branch based on maint-2.4.0 for testing GHC X.Y.Z:

  ```bash
  git checkout maint-2.4.0
  git checkout -b ghc-X.Y.Z
  ```

* Install the tools in the `build-tools` field(s) of the `Agda.cabal`
  file.

* Install Agda using GHC X.Y.Z.

  `make install-bin`

* Run the test-suite, using `make test`.

* Test the different flags for installing Agda describes in the
  `Agda.cabal` file.

* Ensure that cabal haddock works (requires at least cabal-install
  version 1.20.0.3 using version 1.20.0.2 of the Cabal library):

  `cabal configure && cabal haddock`

* Test the fix-agda-whitespace program:

  `make install-fix-agda-whitespace`

* Test the hTags program:

  `make TAGS`

* Test the size-solver program:

  ```bash
  make install-size-solver
  make test-size-solver
  ```

* Commit your changes.

* Merge the ghc-X.Y.Z branch in the maint-2.4.0 branch and push it:

  ```bash
  git checkout maint-2.4.0
  git merge ghc-X.Y.Z
  git push
  ```

* Merge the ghc-X.Y.Z branch in the master branch:

  ```bash
  git checkout master
  git merge ghc-X.Y.Z
  ```

* Delete the ghc-X.Y.Z branch.

* If necessary, install new tools in the `build-tools` field(s) of the
  `Agda.cabal` file.

* Run the test-suite, using `make test`.

* Test the different flags for installing Agda describes in the
  `Agda.cabal` file.

* Ensure that cabal haddock works (requires at least cabal-install
  version 1.20.0.3 using version 1.20.0.2 of the Cabal library):

  `cabal configure && cabal haddock`

* If necessary, commit your changes.

* Push to the master branch.

* Travis:

  - Add GHC X.Y.Z to the `.travis.yml` file in both branches.

  - When the Travis instance for GHC X.Y.Z have passed in both
    branches, update the `tested-with` field in the `Agda.cabal`,
    `fix-agda-whitespace.cabal` and `hTags.cabal` files in both
    branches.
