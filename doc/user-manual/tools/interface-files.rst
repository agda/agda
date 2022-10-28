.. _interface-files:

***************
Interface files
***************

.. note::
   This is a stub. Contributions, additions and corrections are greatly
   appreciated.

When an ``.agda`` file is saved, another file with the same name and extension
``.agdai`` is automatically created. The latter file is what we call an
**interface file**.

Interface files store the results from the type-checking process. These
results include:

* A translation of pattern-matching definitions to case trees (this translation
  speeds up computation).

* The resolution of all implicit arguments.
  (Note: under the option :option:`--allow-unsolved-metas` not **all** implicit arguments
  need to be resolved to create an interface file.)

Storage
-------

In projects that do not use any Agda library, the ``.agdai`` files are
stored alongside the ``.agda`` source file.

If the ``.agda`` source file is part of a project with an *identifiable root*
(i.e. if there is an ``.agda-lib`` file in any of the directories above it),
then the interface file is stored in the ``_build/VERSION`` directory at the
identified root. This prevents losing the interface file when switching between
agda versions. You can revert this behaviour with the option :option:`--no-libraries`.

.. note::
   When an ``.agda`` file is renamed, the old ``.agdai`` file is kept, and a new
   ``.agdai`` file is created. This is the intended behavior, and the orphan
   files can be safely deleted from the user's file system if needed.

The compression run to create ``.agdai`` files introduces sharing. Sharing
improves the memory efficiency of the code loaded from interface files.

The syntax represented in ``.agdai`` files differs significantly from the syntax
of source files.

Compilation
-----------

An external module is loaded by loading its interface file. Interface files are
also intermediate points when compiling through a backend to e.g. Haskell.
