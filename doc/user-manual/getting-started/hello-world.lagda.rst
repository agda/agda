
..
  ::
  module getting-started.hello-world where

.. _hello-world:

*********************
'Hello world' in Agda
*********************

This section contains two minimal Agda programs that can be used to
test if you have installed Agda correctly: one for using Agda
interactively as a proof assistant, and one for compiling Agda
programs to an executable binary. For a more in-depth introduction to
using Agda, see :ref:`A taste of Agda <a-taste-of-agda>` or the
:ref:`list of tutorials <tutorial-list>`.

Hello, Agda!
============

Below is is a small 'hello world' program in Agda (defined in a file
``hello.agda``).

.. code-block:: agda

  data Greeting : Set where
    hello : Greeting

  greet : Greeting
  greet = hello

This program defines a :ref:`data type <data-types>` called
``Greeting`` with one constructor ``hello``, and a :ref:`function
definition <function-definitions>` ``greet`` of type ``Greeting`` that
returns ``hello``.

To load the Agda file, open it in Emacs and load it by pressing ``C-c
C-l`` (``Ctrl+c`` followed by ``Ctrl+l``). You should now see that the
code is highlighted and there should be a message ``*All done*``. If
this is the case, congratulations! You have correctly installed Agda
and the Agda mode for Emacs. If you also want to compile your Agda
programs, continue with the next section.

Hello, World!
=============

Below is a complete executable 'hello world' program in Agda (defined
in a file ``hello-world.agda``)

.. code-block:: agda

  module hello-world where

  open import IO

  main = run (putStrLn "Hello, World!")

To compile the Agda file, either open it in Emacs and press ``C-c C-x
C-c`` or run ``agda --compile hello-world.agda`` from the command
line.

A quick line-by-line explanation:

* Agda programs are structured in :ref:`modules <module-system>`. The
  first module in each file is the *top-level* module whose name
  matches the filename. The contents of a module are declaration such
  as :ref:`data types <data-types>` and :ref:`function definitions
  <function-definitions>`.

* Other modules can be imported using an ``import`` statement, for
  example ``open import IO``. This imports the `IO` module from the
  `standard library <std-lib_>`_ and brings its contents into scope.

* A module exporting a function ``main : IO a`` can be :ref:`compiled
  <compiling-agda-programs>` to a standalone executable.  For example:
  ``main = run (putStrLn "Hello, World!")`` runs the ``IO`` command
  ``putStrLn "Hello, World!"`` and then quits the program.

.. _std-lib: https://github.com/agda/agda-stdlib
