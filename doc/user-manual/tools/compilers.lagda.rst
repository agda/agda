..
  ::
  {-# OPTIONS --erasure #-}
  module tools.compilers where

  open import Agda.Builtin.Nat

.. _compilers:

***********
Compilers
***********

.. contents::
   :depth: 2
   :local:

See also :ref:`foreign-function-interface`.

.. _compiler-backends:

Backends
--------

.. _ghc-backend:

GHC Backend
~~~~~~~~~~~

The GHC backend translates Agda programs into GHC Haskell programs.

Usage
^^^^^

The GHC backend can be invoked from the command line using the flag
:option:`--compile` or :option:`--ghc`:

.. code-block:: bash

  agda --compile [--compile-dir=<DIR>] [--ghc-flag=<FLAG>]
    [--ghc-strict-data] [--ghc-strict] <FILE>.agda

When the flag :option:`--ghc-strict-data` is used, inductive data and record
constructors are compiled to constructors with strict arguments.
(This does not apply to certain builtin types—lists, the maybe type, and
some types related to reflection—and might not apply to types with
``COMPILE GHC … = data …`` pragmas.)

When the flag :option:`--ghc-strict` is used, the GHC backend generates
mostly strict code.  Note that functions might not be strict in unused
arguments, and that function definitions coming from ``COMPILE GHC``
pragmas are not affected. This flag implies :option:`--ghc-strict-data`,
and the exceptions of that flag applies to this flag as well.
(Note that this option requires the use of GHC 9 or later.)

Options
~~~~~~~

.. option:: --compile, --ghc

     Compile to GHC Haskell placing the files in subdirectory ``MAlonzo`` or the directory given by :option:`--compile-dir`.
     Then invoke ``ghc`` (or the compiler given by :option:`--with-compiler`) on the main file,
     unless option :option:`--ghc-dont-call-ghc` is given.

.. option:: --ghc-dont-call-ghc

     Only produce Haskell files, skip the compilation to binary.

.. option:: --ghc-flag={GHC-FLAG}

     Pass flag :samp:`{GHC-FLAG}` to the Haskell compiler.  This option can be given several times.

.. option:: --ghc-strict-data

     Compile Agda constructor to strict Haskell constructors.

.. option:: --ghc-strict

     Generate strict Haskell code.


Pragmas
^^^^^^^

Example
^^^^^^^

The following "Hello, World!" example requires some :ref:`built-ins`
and uses the :ref:`foreign-function-interface`:

::

  module HelloWorld where

  open import Agda.Builtin.IO
  open import Agda.Builtin.Unit
  open import Agda.Builtin.String

  postulate
    putStrLn : String → IO ⊤

  {-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
  {-# COMPILE GHC putStrLn = Text.putStrLn #-}

  main : IO ⊤
  main = putStrLn "Hello, World!"

After compiling the example

.. code-block:: bash

  agda --compile HelloWorld.agda

you can run the HelloWorld program which prints ``Hello, World!``.

.. warning:: Frequent error when compiling: ``Float`` requires the
  `ieee754 <http://hackage.haskell.org/package/ieee754>`_ haskell library.
  Usually ``cabal v1-install ieee754`` or ``cabal v2-install --lib ieee754``
  in the command line does the trick.

.. _javascript-backend:

JavaScript Backend
~~~~~~~~~~~~~~~~~~

The JavaScript backend translates Agda code to JavaScript code.

Usage
^^^^^

The JavaScript backend can be invoked from the command line using the flag :option:`--js`:

.. code-block:: bash

  agda --js [--js-optimize] [--js-minify] [--compile-dir=<DIR>] <FILE>.agda

The :option:`--js-optimize` flag makes the generated JavaScript code
typically faster and less readable.

The :option:`--js-minify` flag makes the generated JavaScript code
smaller and less readable.

Agda can currently generate either CommonJS (used by NodeJS) flavour modules or
AMD (for in-browser usage) flavour modules which can be toggled by :option:`--js-cjs`
(default) and :option:`--js-amd` flags.

Options
~~~~~~~

.. option:: --js

     Compile to JavaScript, placing translation of module :samp:`{M}` into file :samp:`jAgda.{M}.js`.
     The files will be placed into the root directory of the compiled Agda project,
     or into the directory given by :option:`--compile-dir`.

.. option:: --js-amd

     Produce AMD style modules.

.. option:: --js-cjs

     Produce CommonJS style modules.
     This is the default.

.. option:: --js-minify

     Produce minified JavaScript (e.g. omitting whitespace where possible).

.. option:: --js-optimize

     Produce optimized JavaScript.

.. option:: --js-verify

     Except for the main module, run the generated modules through ``node``,
     to verify absence of syntax errors.


Optimizations
-------------

.. _compile-nat:

Builtin natural numbers
~~~~~~~~~~~~~~~~~~~~~~~

Builtin natural numbers are represented as arbitrary-precision integers.
The builtin functions on natural numbers are compiled to the corresponding
arbitrary-precision integer functions.

Note that pattern matching on an Integer is slower than on an unary
natural number. Code that does a lot of unary manipulations
and doesn't use builtin arithmetic likely becomes slower
due to this optimization. If you find that this is the case,
it is recommended to use a different, but
isomorphic type to the builtin natural numbers.


Irrelevant fields and constructor arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Record fields and constructor arguments marked :ref:`irrelevant<irrelevance>`
or :ref:`runtime irrelevant<runtime-irrelevance>` are completely erased from
the compiled record or data type. For instance, ::

  postulate Parity : Nat → Set

  record PNat : Set where
    field
      n    : Nat
      .p   : Parity n
      @0 q : Parity (suc n)

gets compiled by the GHC backend to (up to naming)

.. code-block:: haskell

  newtype PNat = PNat'constructor Integer


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
