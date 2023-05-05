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

If an Agda file has one or more
:ref:`associated<The_agda-lib_files_associated_to_a_given_Agda_file>`
``.agda-lib`` files, then the *project root* is the directory
containing these files. In that case the Agda file's interface file is
stored in the directory ``_build/VERSION`` under the project root.
Different directories are used for different versions of Agda so that
one can switch between versions without losing the interface files.

If an Agda file does not have any associated ``.agda-lib`` file, then
its ``.agdai`` file is stored in the same directory as the Agda file.
(With at least one exception, see `Agda bug #6134
<https://github.com/agda/agda/issues/6134>`_.)

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
