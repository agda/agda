.. _compilers:

***********
Compilers
***********

.. contents::
   :depth: 2
   :local:

Backends
--------

GHC Backend
~~~~~~~~~~~

.. note::
  The Agda GHC backend translates Agda programs into GHC programs.

Usage
^^^^^

The backend can be invoked from the command line using the flag
``--compile``:

.. code-block:: bash

  agda --compile [--compile-dir=<DIR>] [--ghc-flag=<FLAG>] <FILE>.agda

Pragmas
^^^^^^^

Example
^^^^^^^

The following "Hello, World!" example requires some :ref:`built-ins`
and `Pragmas`_:

.. code-block:: agda

  module HelloWorld where

  {-# IMPORT Data.Text.IO #-}

  data Unit : Set where
    unit : Unit

  {-# COMPILED_DATA Unit () () #-}

  postulate
    String : Set

  {-# BUILTIN STRING String #-}

  postulate
    IO : Set → Set

  {-# BUILTIN IO IO #-}
  {-# COMPILED_TYPE IO IO #-}

  postulate
    putStr : String → IO Unit

  {-# COMPILED putStr Data.Text.IO.putStr #-}

  main : IO Unit
  main = putStr "Hello, World!"

After compiling the example

.. code-block:: bash

  agda --compile HelloWorld.agda

you can run the HelloWorld program which prints ``Hello, World!``.


UHC Backend
~~~~~~~~~~~

.. note::
   This backend is available from Agda 2.5.1 on.
   The Agda Standard Library has been updated to support this new backend.
   This backend is currently experimental.

The Agda UHC backend targets the Core language of the Utrecht Haskell Compiler (UHC).
This backend works on the Mac and Linux platforms and requires GHC 7.10.

The backend is disabled by default, as it will pull in some large
dependencies. To enable the backend, use the "uhc" cabal flag when
installing Agda:

.. code-block:: bash

  cabal install Agda -fuhc

The backend also requires UHC to be installed. UHC is not available on
Hackage and needs to be installed manually. This version of Agda has been
tested with UHC 1.1.9.2, using other UHC versions may cause problems.
To install UHC, the following commands can be used:

.. code-block:: bash

  cabal install uhc-util-0.1.6.3 uulib-0.9.21
  wget https://github.com/UU-ComputerScience/uhc/archive/v1.1.9.2.tar.gz
  tar -xf v1.1.9.2.tar.gz
  cd uhc-1.1.9.2/EHC
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

.. _compile-nat:

Builtin natural numbers
~~~~~~~~~~~~~~~~~~~~~~~

.. note::
   GHC/UHC backend only.

Builtin natural numbers are now properly represented as Haskell
Integers, and the builtin functions on natural numbers are compiled to
their corresponding Haskell functions.

Note that pattern matching on an Integer is slower than on an unary
natural number. Code that does a lot of unary manipulations
and doesn't use builtin arithmetic likely becomes slower
due to this optimization. If you find that this is the case,
it is recommended to use a different, but
isomorphic type to the builtin natural numbers.


Erasable types
~~~~~~~~~~~~~~

A data type is considered *erasable* if it has a single constructor whose
arguments are all erasable types, or functions into erasable types. The
compilers will erase

- calls to functions into erasable types
- pattern matches on values of erasable type

At the moment the compilers only have enough type information to erase calls of
top-level functions that can be seen to return a value of erasable type without
looking at the arguments of the call. In other words, a function call will not
be erased if it calls a lambda bound variable, or the result is erasable for
the given arguments, but not for others.

Typical examples of erasable types are the equality type and the accessibility
predicate used for well-founded recursion::

  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x

  data Acc {a} {A : Set a} (_<_ : A → A → Set a) (x : A) : Set a where
    acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x

The erasure means that equality proofs will (mostly) be erased, and never
looked at, and functions defined by well-founded recursion will ignore the
accessibility proof.

