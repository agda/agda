..
  ::
  module tools.compilers where

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

The backend can be invoked from the command line using the flag
``--compile``:

.. code-block:: bash

  agda --compile [--compile-dir=<DIR>] [--ghc-flag=<FLAG>] <FILE>.agda

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

Required libraries for the :ref:`built-ins`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

- ``primFloatEquality`` requires the `ieee754
  <http://hackage.haskell.org/package/ieee754>`_ library.


.. _javascript-backend:

JavaScript Backend
~~~~~~~~~~~~~~~~~~

The JavaScript backend translates Agda code to JavaScript code.

Usage
^^^^^

The backend can be invoked from the command line using the flag
``--js``:

.. code-block:: bash

  agda --js [--js-optimize] [--js-minify] [--compile-dir=<DIR>] <FILE>.agda

The ``--js-optimize`` flag makes the generated JavaScript code
typically faster and less readable.

The ``--js-minify`` flag makes the generated JavaScript code
smaller and less readable.


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
