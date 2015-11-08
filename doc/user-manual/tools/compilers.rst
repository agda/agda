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

