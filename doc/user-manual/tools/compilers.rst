.. _compilers:

***********
Compilers
***********

Backends
--------

GHC Backend
~~~~~~~~~~~

.. note::
   This is a stub.

The Agda GHC compiler can be invoked from the command line using the
flag ``--compile``:

.. code-block:: bash

  agda --compile [--compile-dir=<DIR>]
      [--ghc-flag=<FLAG>] <FILE>.agda

UHC Backend
~~~~~~~~~~~

.. note::
   This backend is available from Agda 2.4.4 on.
   The Agda Standard Library has been updated to support this new backend.

The Agda UHC backend targets the Core language of the Utrecht Haskell Compiler (UHC).
This backend is currently experimental, but should work for most Agda code.

The backend is disabled by default, as it will pull in some large
dependencies. To enable the backend, use the "uhc" cabal flag when
installing Agda:

.. code-block:: bash

  cabal install Agda -fuhc

The backend also requires UHC to be installed. UHC is not available on
Hackage and needs to be installed manually. This version of Agda has been
tested with UHC 1.1.9.0, using other UHC versions may cause problems.
To install UHC, the following commands can be used:

.. code-block:: bash

  git clone https://github.com/UU-ComputerScience/uhc.git
  cd uhc
  git checkout 82149a515aa0cbc492d8aa3f1ff10850a9cbe8d8
  cd EHC
  ./configure
  make
  make install

The Agda UHC compiler can be invoked from the command line using the
flag ``--uhc``:

.. code-block:: bash

  agda --uhc [--compile-dir=<DIR>]
      [--uhc-bin=<UHC>] [--uhc-dont-call-uhc] <FILE>.agda

JavaScript Backend
~~~~~~~~~~~~~~~~~~

.. note::
   This is a stub.

Optimizations
-------------

Builtin natural numbers
~~~~~~~~~~~~~~~~~~~~~~~

.. note::
   GHC/UHC backend only.

Builtin natural numbers are now properly represented as Haskell
Integers, and the builtin functions on natural numbers are compiled to
their corresponding Haskell functions.

Note that pattern matching on an Integer is slower than on an unary
natural number. Code that does a lot of unary manipulations
and doesn't use builtin arithmentic likely becomes slower
due to this optimization. If you find that this is the case,
it is recommended to use a different, but
isomorphic type to the builtin natural numbers.


Pattern matches
~~~~~~~~~~~~~~~

.. note::
   GHC/UHC backend only.

Pattern matches with a single alternative are compiled to a lazy
match (using 'let' instead of 'case'). This means that matching on
'refl' will not force the proof, and programs using well-founded
recursion will be lazy in the accessibility proof.

