..
  ::
  module language.mutual-recursion where

  open import Agda.Builtin.Nat
  open import Agda.Builtin.Bool


.. _mutual-recursion:

****************
Mutual Recursion
****************

Agda offers multiple ways to write mutually-defined data types, record types and functions.

- :ref:`mutual-recursion-mutual-block`
- :ref:`mutual-recursion-forward-declaration`
- :ref:`mutual-recursion-interleaved-mutual`

The last two are more expressive than the first one as they allow the interleaving of
declarations and definitions thus making it possible for some types to refere to the
constructors of a mutually-defined datatype.

.. _mutual-recursion-interleaved-mutual:

Interleaved mutual blocks
-------------------------

Mutual recursive functions can be written by placing them inside an ``interleaved mutual``
block. The type signature of each function must come before its defining clauses and its
usage sites on the right-hand side of other functions.
The clauses for different functions can be interleaved e.g. for pedagogical purposes::

  interleaved mutual

    -- Declarations:
    even : Nat → Bool
    odd  : Nat → Bool

    -- zero is even, not odd
    even zero = true
    odd  zero = false

    -- suc case: switch evenness on the predecessor
    even (suc n) = odd n
    odd  (suc n) = even n

You can mix arbitrary declarations, such as modules and postulates, with mutually recursive
definitions. For data types and records the following syntax is used to separate the
declaration from the introduction of constructors in one or many ``constructor`` blocks::

  interleaved mutual

    -- Declaration of a product record, a universe of codes, and a decoding function
    record _×_ (A B : Set) : Set
    data U : Set
    El : U → Set

    -- We have a code for the type of natural numbers in our universe
    constructor `Nat : U
    El `Nat = Nat

    -- Btw we know how to pair values in a record
    record _×_ A B where
      constructor _,_
      inductive
      field fst : A; snd : B

    -- And we have a code for pairs in our universe
    constructor _`×_ : (A B : U) → U
    El (A `× B) = El A × El B

  -- we can now build types of nested pairs of natural numbers
  ty-example : U
  ty-example = `Nat `× ((`Nat `× `Nat) `× `Nat)

  -- and their values
  val-example : El ty-example
  val-example = 0 , ((1 , 2) , 3)


These mutual blocks get desugared into the forward declaration blocks described below by:

- leaving the signatures where they are
- grouping the clauses for a function together with the first of them
- grouping the constructors for a datatype together with the first of them

.. _mutual-recursion-forward-declaration:

Forward declaration
-------------------

Mutual recursive functions can be written by placing the type signatures of all mutually
recursive function before their definitions. The span of the mutual block will be
automatically inferred by Agda:

.. code-block:: agda

  f : A
  g : B[f]
  f = a[f, g]
  g = b[f, g].

You can mix arbitrary declarations, such as modules and postulates, with mutually recursive definitions.
For data types and records the following syntax is used to separate the declaration from the definition:
::

  -- Declaration.
  data Vec (A : Set) : Nat → Set  -- Note the absence of ‘where’.

  -- Definition.
  data Vec A where  -- Note the absence of a type signature.
    []   : Vec A zero
    _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

  -- Declaration.
  record Sigma (A : Set) (B : A → Set) : Set

  -- Definition.
  record Sigma A B where
    constructor _,_
    field fst : A
          snd : B fst

The parameter lists in the second part of a data or record declaration behave like
variables left-hand sides (although infix syntax is not supported). That is, they
should have no type signatures, but implicit parameters can be omitted or bound by name.

..
  ::
  module Universe where

Such a separation of declaration and definition is for instance needed when defining a set of codes for types and their interpretation as actual types (a so-called *universe*)::

    -- Declarations.
    data TypeCode : Set
    Interpretation : TypeCode → Set

    -- Definitions.
    data TypeCode where
      nat : TypeCode
      pi  : (a : TypeCode) (b : Interpretation a → TypeCode) → TypeCode

    Interpretation nat      = Nat
    Interpretation (pi a b) = (x : Interpretation a) → Interpretation (b x)

When making separated declarations/definitions private or abstract you should attach the ``private`` keyword to the declaration and the ``abstract`` keyword to the definition. For instance, a private, abstract function can be defined as

..
  ::
  module private-abstract (A : Set) (e : A) where

::

    private
      f : A
    abstract
      f = e


.. _mutual-recursion-mutual-block:

Old-style ``mutual`` blocks
----------------------------

.. note::
   You are advised to avoid using this old syntax if possible, but the old syntax
   is still supported.

Mutual recursive functions can be written by placing the type signatures of all mutually
recursive function before their definitions:

.. code-block:: agda

  mutual
    f : A
    f = a[f, g]

    g : B[f]
    g = b[f, g]

Using the ``mutual`` keyword,
the *universe* example from above is expressed as follows::

  mutual
    data TypeCode : Set where
      nat : TypeCode
      pi  : (a : TypeCode) (b : Interpretation a → TypeCode) → TypeCode

    Interpretation : TypeCode → Set
    Interpretation nat      = Nat
    Interpretation (pi a b) = (x : Interpretation a) → Interpretation (b x)

This alternative syntax desugars into the new syntax.
