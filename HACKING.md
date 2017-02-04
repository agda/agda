Testing and documenting your changes
------------------------------------

When you implement a new feature of fix a bug:

1. Document it in `CHANGELOG.md`.

2. Test your changes by running

   ```
   make clean
   make test
   ```

Where to commit changes
-----------------------

    CURRENT_AGDA = current released Agda version, e.g. 2.4.2.5
    AGDA_MAINT   = Agda maintenance version, e.g. 2.4.2.6

A. Your change is independent of Agda

   1. Push your commit in the `CURRENT_AGDA` branch
   2. Merge the `CURRENT_AGDA` branch into the `AGDA_MAINT` branch
   3. Merge the `AGDA_MAINT` branch into the master branch

B. Your change is due to a change in the `AGDA_MAINT` version of Agda

   1. Push your commit in the `AGDA_MAINT` branch
   2. Merge the `AGDA_MAINT` branch into the master branch

C. Your change is due to a change in the master version of Agda

   1. Push your commit in the master branch

This scheme should guarantee that:

  a. the stdlib `CURRENT_AGDA` branch always builds with the current
     released Agda version,

  b. the stdlib `AGDA_MAINT` branch always build with the Agda maint
     branch and

  c. the stdlib master branch always builds with the Agda master
     branch.
