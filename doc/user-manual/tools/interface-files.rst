.. _interface-files:

********************
Interface files
********************

.. note::
   This is a stub. Contributions, additions and corrections are greatly
   appreciated.

Probably you already noticed that when you save an agda file, another file
with the same name and extension .agdai is automatically created. This .agdai
file is what we call an **interface file** that stores a compressed form of
the type-checked version of the code that lives in the corresponding .agda file.

Interface files store the results from the type-checking process and resolve
all implicit arguments (unless you use the flag ``--allow-unsolved-metas``).
Formally, an .agdai file is a compiled version of the agda source code that can
be executed by the Agda machine.

Interface files are intended to make operations faster. They translate
pattern-matching definitions to case trees (this translation speeds up
computation).

.. note::
   When an agda file is renamed, the old .agdai file is kept, and a new .agdai
   file is created. This is the intended behavior, but you can delete the orphan
   files from your file system if you wish.

Expression trees
--------------------

An expression tree provides a method of translating source code (in our
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
