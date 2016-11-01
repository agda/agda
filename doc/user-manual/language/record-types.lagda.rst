..
  ::
  module language.record-types where

  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat hiding (_==_; _<_)

  _||_ : Bool → Bool → Bool
  true  || x = true
  false || x = x

.. _record-types:

************
Record Types
************

.. note::
   This is a stub.

.. _record-modules:

Record modules
--------------

.. _eta-expansion:

Eta-expansion
-------------

.. _instance-fields:

Instance fields
---------------

Instance fields, that is record fields marked with ``{{ }}`` can be used to
model "superclass" dependencies. For example::

  record Eq (A : Set) : Set where
    field
      _==_ : A → A → Bool

  open Eq {{...}}

.. code-block:: agda

  record Ord (A : Set) : Set where
    field
      _<_ : A → A → Bool
      {{eqA}} : Eq A

  open Ord {{...}} hiding (eqA)

Now anytime you have a function taking an ``Ord A`` argument the ``Eq A`` instance
is also available by virtue of η-expansion. So this works as you would expect:

.. code-block:: agda

  _≤_ : {A : Set} {{OrdA : Ord A}} → A → A → Bool
  x ≤ y = (x == y) || (x < y)

There is a problem however if you have multiple record arguments with conflicting
instance fields. For instance, suppose we also have a ``Num`` record with an ``Eq`` field

.. code-block:: agda

  record Num (A : Set) : Set where
    field
      fromNat : Nat → A
      {{eqA}} : Eq A

  open Num {{...}} hiding (eqA)

  _≤3 : {A : Set} {{OrdA : Ord A}} {{NumA : Num A}} → A → Bool
  x ≤3 = (x == fromNat 3) || (x < fromNat 3)

Here the ``Eq A`` argument to ``_==_`` is not resolved since there are two conflicting
candidates: ``Ord.eqA OrdA`` and ``Num.eqA NumA``. To solve this problem you can declare
instance fields as *overlappable* using the ``overlap`` keyword::

  record Ord (A : Set) : Set where
    field
      _<_ : A → A → Bool
      overlap {{eqA}} : Eq A

  open Ord {{...}} hiding (eqA)

  record Num (A : Set) : Set where
    field
      fromNat : Nat → A
      overlap {{eqA}} : Eq A

  open Num {{...}} hiding (eqA)

  _≤3 : {A : Set} {{OrdA : Ord A}} {{NumA : Num A}} → A → Bool
  x ≤3 = (x == fromNat 3) || (x < fromNat 3)

Whenever there are multiple valid candidates for an instance goal, if **all** candidates
are overlappable, the goal is solved by the left-most candidate. In the example above
that means that the ``Eq A`` goal is solved by the instance from the ``Ord`` argument.

Clauses for instance fields can be omitted when defining values of record
types. For instance we can define ``Nat`` instances for ``Eq``, ``Ord`` and
``Num`` as follows, leaving out cases for the ``eqA`` fields::

  instance
    EqNat : Eq Nat
    _==_ {{EqNat}} = Agda.Builtin.Nat._==_

    OrdNat : Ord Nat
    _<_ {{OrdNat}} = Agda.Builtin.Nat._<_

    NumNat : Num Nat
    fromNat {{NumNat}} n = n
