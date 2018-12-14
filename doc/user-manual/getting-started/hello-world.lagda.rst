
*********************
'Hello world' in Agda
*********************

Agda programs are structured in :ref:`modules <module-system>`. The
first module in each file is the *top-level* module whose name matches
the filename:

::

  module hello-world where

The contents of a module are declaration such as :ref:`data types
<data-types>` and :ref:`function definitions <function-definitions>`.

Other modules can be imported using an ``import`` statement, for
example:

::

  open import IO

This imports the `IO` module from the `standard library <std-lib_>`_.

.. _std-lib: https://github.com/agda/agda-stdlib

A module exporting a function ``main : IO a`` can be :ref:`compiled
<compiling-agda-programs>` to a standalone executable.  For example:

::

  main = run (putStrLn "Hello, World!")

The complete 'hello world' program in Agda would thus be defined in a
file ``hello-world.agda`` and look as follows:

.. code-block:: agda

  module hello-world where

  open import IO

  main = run (putStrLn "Hello, World!")


To compile the Agda file, either open it in Emacs and press ``C-c C-x
C-c`` or run ``agda --compile hello-world.agda`` from the command
line.
