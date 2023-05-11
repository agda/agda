
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

  open import Agda.Builtin.IO using (IO)
  open import Agda.Builtin.Unit using (⊤)
  open import Agda.Builtin.String using (String)

  postulate putStrLn : String → IO ⊤
  {-# FOREIGN GHC import qualified Data.Text as T #-}
  {-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}

  main : IO ⊤
  main = putStrLn "Hello world!"

This code is self-contained and has several declarations:

1. Imports of the ``IO``, ``⊤`` and ``String`` types from the Agda Builtin
   library.
2. A postulate of the function type ``putStrLn``.
3. Two :ref:`pragmas <pragmas>` that tell Agda how to compile the function ``putStrLn``.
4. A definition of the function ``main``.

To compile the Agda file, either open it in Emacs and press ``C-c C-x
C-c`` or run ``agda --compile hello-world.agda`` from the command
line. This will create a binary ``hello-world`` in the current
directory that prints ``Hello world!``. To find out more about the
``agda`` command, use ``agda --help``.

.. note::

   As you can see from this example, by default Agda includes only
   minimal library support through the ``Builtin`` modules. The `Agda
   Standard Library <std-lib_>`_ provides bindings for most commonly
   used Haskell functions, including ``putStrLn``.  For a version of
   this 'hello world' program that uses the standard library, see
   :ref:`building-an-executable-agda-program`.

.. _std-lib: https://github.com/agda/agda-stdlib
