.. _interface-files:

********************
Interface files
********************

.. note::
   This is a stub. Contributions, additions and corrections are greatly
   appreciated.

Probably you already noticed that when you save an agda file, another file
with the same name and extension .agdai is automatically created. This .agdai
file is what we call an **interface file**.

Interface files store the results from the type-checking process. These
results include:

* A translation of pattern-matching definitions to case trees (this translation
  speeds up computation).

* The resolution of all implicit arguments (optional, you can avoid this by
  using the flag ``--allow-unsolved-metas``).

The .agdai files are stored alongside the .agda source file.

Only if the .agda source file is part of a project with an *identifiable root*
(i.e. if there is an .agda-lib file in any of the directories above it), then
the interface file is stored in the ``_build/VERSION`` directory at the
identified root. This prevents losing the interface file when switching between
agda versions. You can revert this behaviour with the flag ``--no-project``.

.. note::
   When an agda file is renamed, the old .agdai file is kept, and a new .agdai
   file is created. This is the intended behavior, but you can delete the orphan
   files from your file system if you wish.

Expression trees
--------------------

An expression tree is the result of translating a given source code (in our
case, the .agda file) into a data structure (the corresponding .agdai file).

The compression run to create .agdai files introduces sharing in the expression
trees. Sharing improves the memory efficiency of the code loaded from interface
files.

The syntax represented in .agdai files significantly differs from the syntax
of source files.

Compilation
--------------------

An external module is loaded by loading its interface file. Interface files are
also intermediate points when compiling through a backend to e.g. Haskell.
