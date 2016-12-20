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

.. contents::
   :depth: 2
   :local:

.. note::
   This is a stub.

.. _record-declarations:

Record declarations
-------------------

Record types can be declared using the ``record`` keyword

..
  ::
  module Hide where

::

   record Pair (A B : Set) : Set where
     field
       fst : A
       snd : B

This defines a new type ``Pair : Set → Set → Set`` and two projection functions

.. code-block:: agda

  Pair.fst : {A B : Set} → Pair A B → A
  Pair.snd : {A B : Set} → Pair A B → B

Elements of record types can be defined using a record expression

::

   p23 : Pair Nat Nat
   p23 = record { fst = 2; snd = 3 }

or using :ref:`copatterns`

::

   p34 : Pair Nat Nat
   Pair.fst p34 = 3
   Pair.snd p34 = 4

Record types behaves much like single constructor datatypes (but see
`eta-expansion`_ below), and you can name the constructor using the ``constructor`` keyword

::

  record Pair (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B

  p45 : Pair Nat Nat
  p45 = 4 , 5

.. note::
   Naming the constructor is not required to enable pattern matching against
   record values. Record expression can appear as patterns.

.. _record-modules:

Record modules
--------------

.. _eta-expansion:

Along with a new type, a record declaration also defines a module containing
the projection functions. This allows records to be "opened", bringing the
fields into scope. For instance

::

  swap : {A B : Set} → Pair A B → Pair B A
  swap p = snd , fst
    where open Pair p

It possible to add arbitrary definitions to the record module, by defining them
inside the record declaration

::

  record Functor (F : Set → Set) : Set₁ where
    field
      fmap : ∀ {A B} → (A → B) → F A → F B

    _<$_ : ∀ {A B} → A → F B → F A
    x <$ fb = fmap (λ _ → x) fb

.. note::
   In general new definitions need to appear after the field declarations, but
   simple non-recursive function definitions without pattern matching can be
   interleaved with the fields. The reason for this restriction is that the
   type of the record constructor needs to be expressible using :ref:`let-expressions`.
   In the example below ``D₁`` can only contain declarations for which the
   generated type of ``mkR`` is well-formed.

   .. code-block:: agda

      record R Γ : Setᵢ where
        constructor mkR
        field f₁ : A₁
        D₁
        field f₂ : A₂

      mkR : ∀ {Γ} (f₁ : A₁) (let D₁) (f₂ : A₂) → R Γ

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

