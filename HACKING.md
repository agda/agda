Contributing to the library
===========================

Thank you for your interest in contributing to the Agda standard library. Hopefully this guide should make it easy to do so! Feel free to ask any questions on the Agda mailing list.

How to make changes
-------------------

### Fork and download the repository

1. Create a fork by clicking `Fork` button at the top right of the [repository](https://github.com/agda/agda-stdlib).
2. On the command line, and in a suitable folder, download your fork by running the command
   ```
   git clone https://github.com/USER_NAME/agda-stdlib agda-stdlib-fork
   ```

   where `USER_NAME` is your Git username. The folder `agda-stdlib-fork` should now contain a copy of the standard library.


### Make your changes

3. Make your proposed changes within `agda-stdlib-fork`. Please try to obey existing conventions in the library. See below for a selection of the most important ones.
4. Document your changes in `agda-stdlib-fork/CHANGELOG.md`
5. Ensure your changes are compatible with the rest of the library by running the commands
   ```
   make clean
   make test
   ```
   inside the `agda-stdlib-fork` folder. Continue to correct any bugs thrown up until the tests are passed.

   Your proposed changes MUST pass these tests.

   **Agda versions**: the standard library is developed alongside Agda itself so your fork of the library may not be compatible with the latest official release. If you think this is the case, it may be necessary to download the latest version of the [Agda](https://github.com/agda/agda) repository and install by running (in a suitable folder):
    ```
    git clone https://github.com/agda/agda
    ```
    Enter the folder and run the command:
    ```
    cabal install
    ```

    **Fixing whitespace**: the tests require the use of a tool called `fix-agda-whitespace`. This can be installed by entering the folder of your agda installation (either your main one, or the version obtained by following the instructions in the section above) and running the command
    ```
    make build-fix-agda-whitespace
    ```

### Upload your changes

6. Use the `git add` command to add the files you have changed to your proposed commit.
7. Run the command:
   ```
   git commit
   ```
   and enter a meaningful description for your changes.
8. Upload your changes to your fork by running the command:
   ```
   git push
   ```
9. Go to your fork on Github at `https://github.com/USER_NAME/agda-stdlib` and click the green `Compare & pull request` button to open a pull request.
10. The standard library maintainers will then be made aware of your requested changes and should be in touch soon.

Naming conventions
------------------

### General

    - Names should be descriptive (i.e. given the name of a proof and the module it lives in then users should be able to make a reasonable guess at what it contains).

### Preconditions and postconditions

    - Preconditions should only be included in names of results if "important" (mostly judgement call).
    - Preconditions of results should be prepended to a description of the result by using the symbol `⇒` in names (e.g. `asym⇒antisym`)
    - Preconditions and postconditions should be combined using the symbols `∨` and `∧` (e.g. `i*j≡0⇒i≡0∨j≡0`)
    - Try to avoid the need for bracketing but if necessary use square brackets (e.g. `[m∸n]⊓[n∸m]≡0`)

### Operators and relations

    - Operators and relations should be defined using the misfix notation (e.g. `_+_`, `_<_`)
    - Common properties such as those in rings/orders/equivalences etc. have defined abbreviations (e.g. commutativity is shortened to `comm`). `Data.Nat.Properties` is a good place to look for examples.
    - Properties should be by prefixed by the relevant operator/relation (e.g. commutativity of `_+_` is named `+-comm`)
    - If the relevant unicode characters are available, negated forms of relations should be used over the `¬` symbol (e.g. `m+n≮n` should be used instead of `¬m+n<n`).
