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
  data Vec A where
    []   : Vec A zero
    _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

  -- Declaration.
  record Sigma (A : Set) (B : A → Set) : Set

  -- Definition.
  record Sigma A B where
    constructor _,_
    field fst : A
          snd : B fst

When making separated declarations/definitions private or abstract you should attach the ``private`` keyword to the declaration and the ``abstract`` keyword to the definition. For instance, a private, abstract function can be defined as

..
  ::
  module private-abstract (A : Set) (e : A) where

::

    private
      f : A
    abstract
      f = e

Old Syntax
----------

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

This alternative syntax desugars into the new syntax.
