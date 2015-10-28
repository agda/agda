.. _package-system:

******************
Library Management
******************

Agda has a simple package management system to support working with multiple
libraries in different locations. The central concept is that of a *library*.

Library files
-------------

A library consists of

- a name
- a set of dependencies
- a set of include paths

Libraries are defined in ``.agda-lib`` files with the following syntax:

.. code-block:: none

  name: LIBRARY-NAME  -- Comment
  depend: LIB1 LIB2
    LIB3
    LIB4
  include: PATH1
    PATH2
    PATH3

Dependencies are library names, not paths to ``.agda-lib`` files, and include
paths are relative to the location of the library-file.

Installing libraries
--------------------

To be found by Agda a library file has to be listed (with its full path) in the file
``AGDA_DIR/libraries`` (where ``AGDA_DIR`` defaults to ``~/.agda`` on unix-like systems
and ``C:\Users\USERNAME\AppData\Roaming\agda`` or similar on Windows, and can be
overridden by setting the ``AGDA_DIR`` environment variable).
Environment variables in the paths (of the form ``$VAR`` or ``${VAR}``) are
expanded. The location of the libraries file used can be overridden using the
``--library-file=FILE`` command line option, although this is not expected to
be very useful.

You can find out the precise location of the ``libraries`` file by
calling ``agda -l fjdsk Dummy.agda`` at the command line and looking at the
error message (assuming you don't have a library called ``fjdsk`` installed).

Using a library
---------------

There are three ways a library gets used:

- You supply the ``--library=LIB`` (or ``-l LIB``) option to Agda. This is
  equivalent to adding a ``-iPATH`` for each of the include paths of ``LIB``
  and its (transitive) dependencies.

- No explicit ``--library`` flag is given, and the current project root
  (of the Agda file that is being loaded) or one of its parent directories
  contains an ``.agda-lib`` file defining a library ``LIB``. This library is
  used as if a ``--librarary=LIB`` option had been given, except that it is not
  necessary for the library to be listed in the ``AGDA_DIR/libraries`` file.

- No explicit ``--library`` flag, and no ``.agda-lib`` file in the project
  root. In this case the file ``AGDA_DIR/defaults`` is read and all libraries
  listed are added to the path. The ``defaults`` file should contain a list of
  library names, each on a separate line. In this case the current directory is
  also added to the path.

  To disable default libraries, you can give the flag
  ``--no-default-libraries``.

Version numbers
---------------

Library names can end with a version number (for instance, ``mylib-1.2.3``).
When resolving a library name (given in a ``--library`` flag, or listed as a
default library or library dependency) the following rules are followed:

- If you don't give a version number, any version will do.
- If you give a version number an exact match is required.
- When there are multiple matches an exact match is preferred, and otherwise
  the latest matching version is chosen.

For example, suppose you have the following libraries installed: ``mylib``,
``mylib-1.0``, ``otherlib-2.1``, and ``otherlib-2.3``. In this case, aside from
the exact matches you can also say ``--library=otherlib`` to get
``otherlib-2.3``.

