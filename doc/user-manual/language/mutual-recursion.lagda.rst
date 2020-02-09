..
  ::
  module language.mutual-recursion where

  open import Agda.Builtin.Nat

.. _mutual-recursion:

****************
Mutual Recursion
****************

Mutual recursive functions can be written by placing the type signatures of all mutually recursive function before their definitions:

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

Old Syntax: Keyword ``mutual``
------------------------------

.. note::
   You are advised to avoid using this old syntax if possible, but the old syntax
   is still supported.

Mutual recursive functions can be written by placing the type signatures of all mutually recursive function before their definitions:

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
