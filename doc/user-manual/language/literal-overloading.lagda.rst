..
  ::
  module language.literal-overloading where

  open import Agda.Builtin.Nat
  open import Agda.Primitive
  open import Agda.Builtin.Bool
  open import Agda.Builtin.String

  data   ⊥ : Set where
  record ⊤ : Set where
    instance constructor tt

  data Fin : Nat → Set where
    zero : ∀ {n} → Fin (suc n)
    suc  : ∀ {n} → Fin n → Fin (suc n)

.. _literal-overloading:

*******************
Literal Overloading
*******************

.. _overloaded-nats:

Natural numbers
---------------

By default :ref:`natural number literals <lexical-structure-int-literals>` are
mapped to the :ref:`built-in natural number type <built-in-nat>`. This can be
changed with the ``FROMNAT`` built-in, which binds to a function accepting a
natural number:

.. code-block:: agda

  {-# BUILTIN FROMNAT fromNat #-}

This causes natural number literals ``n`` to be desugared to ``fromNat n``,
whenever ``fromNat`` is in scope *unqualified* (renamed or not).
Note that the desugaring happens before :ref:`implicit argument
<implicit-arguments>` are inserted so ``fromNat`` can have any number of
implicit or :ref:`instance arguments <instance-arguments>`. This can be
exploited to support overloaded literals by defining a :ref:`type class
<instance-arguments>` containing ``fromNat``::

  module number-simple where

    record Number {a} (A : Set a) : Set a where
      field fromNat : Nat → A

    open Number {{...}} public

.. code-block:: agda

   {-# BUILTIN FROMNAT fromNat #-}

This definition requires that any natural number can be mapped into the given
type, so it won't work for types like ``Fin n``. This can be solved by refining
the ``Number`` class with an additional constraint::

  record Number {a} (A : Set a) : Set (lsuc a) where
    field
      Constraint : Nat → Set a
      fromNat : (n : Nat) {{_ : Constraint n}} → A

  open Number {{...}} public using (fromNat)

  {-# BUILTIN FROMNAT fromNat #-}

This is the definition used in ``Agda.Builtin.FromNat``.
A ``Number`` instance for ``Nat`` is simply this::

  instance
    NumNat : Number Nat
    NumNat .Number.Constraint _ = ⊤
    NumNat .Number.fromNat    m = m

A ``Number`` instance for ``Fin n`` can be defined as follows::

  _≤_ : (m n : Nat) → Set
  zero  ≤ n     = ⊤
  suc m ≤ zero  = ⊥
  suc m ≤ suc n = m ≤ n

  fromN≤ : ∀ m n → m ≤ n → Fin (suc n)
  fromN≤ zero    _       _  = zero
  fromN≤ (suc _) zero    ()
  fromN≤ (suc m) (suc n) p  = suc (fromN≤ m n p)

  instance
    NumFin : ∀ {n} → Number (Fin (suc n))
    NumFin {n} .Number.Constraint m         = m ≤ n
    NumFin {n} .Number.fromNat    m {{m≤n}} = fromN≤ m n m≤n

  test : Fin 5
  test = 3

It is important that the constraint for literals is trivial.  Here,
``3 ≤ 5`` evaluates to ``⊤`` whose inhabitant is found by unification.

Using predefined function from the standard library and instance ``NumNat``,
the ``NumFin`` instance can be simply:

.. code-block:: agda

  open import Data.Fin using (Fin; #_)
  open import Data.Nat using (suc; _≤?_)
  open import Relation.Nullary.Decidable using (True)

  instance
    NumFin : ∀ {n} → Number (Fin n)
    NumFin {n} .Number.Constraint m         = True (suc m ≤? n)
    NumFin {n} .Number.fromNat    m {{m<n}} = #_ m {m<n = m<n}



.. _agda-prelude: https://github.com/UlfNorell/agda-prelude

.. _overloaded-negative-numbers:

Negative numbers
----------------

Negative integer literals have no default mapping and can only be used through
the ``FROMNEG`` built-in. Binding this to a function ``fromNeg`` causes
negative integer literals ``-n`` to be desugared to ``fromNeg n``, where ``n``
is a :ref:`built-in natural number <built-in-nat>`. From ``Agda.Builtin.FromNeg``::

  record Negative {a} (A : Set a) : Set (lsuc a) where
    field
      Constraint : Nat → Set a
      fromNeg : (n : Nat) {{_ : Constraint n}} → A

  open Negative {{...}} public using (fromNeg)
  {-# BUILTIN FROMNEG fromNeg #-}

.. _overloaded-strings:

Strings
-------

:ref:`String literals <lexical-structure-string-literals>` are overloaded with
the ``FROMSTRING`` built-in, which works just like ``FROMNAT``. If it is not
bound string literals map to :ref:`built-in strings <built-in-string>`. From
``Agda.Builtin.FromString``::

  record IsString {a} (A : Set a) : Set (lsuc a) where
    field
      Constraint : String → Set a
      fromString : (s : String) {{_ : Constraint s}} → A

  open IsString {{...}} public using (fromString)
  {-# BUILTIN FROMSTRING fromString #-}


Restrictions
------------

Currently only integer and string literals can be overloaded.

Overloading does not work in patterns yet.
