.. _literal-overloading:

*******************
Literal Overloading
*******************

Natural numbers
---------------

By default :ref:`natural number literals <lexical-structure-int-literals>` are
mapped to the :ref:`built-in natural number type <built-in-nat>`. This can be
changed with the ``FROMNAT`` built-in, which binds to a function accepting a
natural number::

  {-# BUILTIN FROMNAT fromNat #-}

This causes natural number literals ``n`` to be desugared to ``fromNat n``.
Note that the desugaring happens before :ref:`implicit argument
<implicit-arguments>` are inserted so ``fromNat`` can have any number of
implicit or :ref:`instance arguments <instance-arguments>`. This can be
exploited to support overloaded literals by defining a :ref:`type class
<instance-arguments>` containing ``fromNat``::

  record Number {a} (A : Set a) : Set a where
    field fromNat : Nat → A

  open Number {{...}} public

  {-# BUILTIN FROMNAT fromNat #-}

This definition requires that any natural number can be mapped into the given
type, so it won't work for types like ``Fin n``. This can be solved by refining
the ``Number`` class with an additional constraint::

  record Number {a} (A : Set a) : Set (lsuc a) where
    field
      Constraint : Nat → Set a
      fromNat : ∀ n → {{_ : Constraint n}} → A

  open Number {{...}} public using (fromNat)

  {-# BUILTIN FROMNAT fromNat #-}

This is the definition used in the agda-prelude_ library. A ``Number`` instance
for ``Fin n`` can then be defined as follows::

  natToFin : ∀ {n} (m : Nat) {{_ : IsTrue (m <? n)}} → Fin n

  instance
    NumFin : ∀ {n} → Number (Fin n)
    Number.Constraint (NumFin {n}) k = IsTrue (k <? n)
    Number.fromNat    NumFin       k = natToFin k

.. _agda-prelude: https://github.com/UlfNorell/agda-prelude

Negative numbers
----------------

Negative integer literals have no default mapping and can only be used through
the ``FROMNEG`` built-in. Binding this to a function ``fromNeg`` causes
negative integer literals ``-n`` to be desugared to ``fromNeg n``, where ``n``
is a :ref:`built-in natural number <built-in-nat>`. From the agda-prelude_::

  record Negative {a} (A : Set a) : Set (lsuc a) where
    field
      Constraint : Nat → Set a
      fromNeg : ∀ n → {{_ : Constraint n}} → A

  open Negative {{...}} public using (fromNeg)

  {-# BUILTIN FROMNEG fromNeg #-}

Other types
-----------

Currently only integer literals can be overloaded.

