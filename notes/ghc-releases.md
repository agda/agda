Testing the repository with a new version of GHC
-------

Let's suppose the new version of GHC is X.Y.Z and the current
maintenance branch is maint-2.4.0.

* Create a new branch based on maint-2.4.0 for testing GHC X.Y.Z:

  ````bash
  git checkout maint-2.4.0
  git checkout -b ghc-X.Y.Z
  ````

* Install the tools in the `build-tools` field of the `Agda.cabal`
  file.

* Run the test-suite, using `make test` (which does not work properly
  unless you run `autoreconf` and `./configure` first).

* Ensure that cabal haddock works (requires at least cabal-install
  version 1.20.0.3 using version 1.20.0.2 of the Cabal library):

  `cabal configure && cabal haddock`

* Update the `tested-with` field in the `Agda.cabal` file.

* Test the fix-agda-whitespace program:

  `make install-fix-agda-whitespace`

* Update the `tested-with` field in the `fix-agda-whitespace.cabal` file.

* Test the hTags program:

  ````bash
  rm -f src/full/TAGS
  make TAGS
  ````

* Update the `tested-with` field in the `hTags.cabal` file.

* Commit your changes.

* Merge the ghc-X.Y.Z branch in the maint-2.4.0 branch and push it:

  ````bash
  git merge ghc-X.Y.Z
  git push
  ````

* Merge the ghc-X.Y.Z branch in the master branch:

  ````bash
  git checkout master
  git merge ghc-X.Y.Z
  ```

* Delete the ghc-X.Y.Z branch.

* If necessary, install new tools in the `build-tools` field of the
  `Agda.cabal` file.

* Run the test-suite, using `make test`.

* Ensure that cabal haddock works (requires at least cabal-install
  version 1.20.0.3 using version 1.20.0.2 of the Cabal library):

  `cabal configure && cabal haddock`

* If necessary, commit your changes.

* Push to the master branch.
