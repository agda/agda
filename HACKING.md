Contributing to the library
---------------------------

Thank you for your interest in contributing to the Agda standard library. Hopefully this guide should make it easy to do so! Feel free to ask any questions on the Agda mailing list.

### Fork and download the repository

1. Create a fork by clicking `Fork` button at the top right of the [repository](https://github.com/agda/agda-stdlib).
2. On the command line, and in a suitable folder, download your fork by running the command
   ```
   git clone https://github.com/USER_NAME/agda-stdlib agda-stdlib-fork
   ```

   where `USER_NAME` is your Git username. The folder `agda-stdlib-fork` should now contain a copy of the standard library.


### Make your changes

3. Make your proposed changes within `agda-stdlib-fork`.
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
    ````

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
