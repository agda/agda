..
  ::
  {-# OPTIONS --two-level --cumulativity #-}

  module language.two-level where

  open import Agda.Primitive
  open import Agda.Builtin.Equality


************
Two-Level Type Theory
************

Basics
------

Two-level type theory (2LTT) refers to versions of Martin-Lof
type theory that combine two type theories: one level as a
homotopy type theory, which may include univalent universes and
higher inductive types, and the second level as a traditional form
of type theory validating uniqueness of identity proofs.

Since version 2.6.2, Agda enables the use of strict (non-fibrant)
type universes ``SSet`` with ``--two-level`` flag. With this option,
Agda adds a new sort ``SSet`` of strict sets. We can define an
equality type for this sort::

  infix 4 _≡ˢ_
  data _≡ˢ_ {a} {A : SSet a} (x : A) : A → SSet a where
    refl : x ≡ˢ x

It satisfies the UIP::

  UIP : {a : Level} {A : SSet a} {x y : A} (p q : x ≡ˢ y) → p ≡ˢ q
  UIP refl refl = refl

.. note::
   In order to work with 2LTT, we use also the fundamental sort ``Set``
   of Agda with the usual identity type ``_≡_``. To make distinction
   between two equalities, we should assume ``--without-K``. This flag
   disables UIP only for ``_≡_``, not for ``_≡ˢ_``. Thus, we indeed
   obtain the two type theories.

.. note::
   Strict Types have various names in the literature. These are `non-fibrant types` in
   [`HTS (2017) <https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/HTS.pdf>`_],
   `outer types` in [`2LTT (2017) <https://arxiv.org/abs/1705.03307>`_], and `exo-types` in
   [`Univalence Principle (2021) <https://arxiv.org/abs/2102.06275>`_]. Besides, the sort ``Set``
   is respresented by fibrant types, inner types, and types in these studies, respectively.

In 2LTT, it is commonly assumed that every type is a strict type. Agda reflects
this idea via the option ``--cumulativity``. The flag enables the rule that ``Set a``
is a  subtype of ``SSet a`` for each ``a : Level``. In this case, the new equality
type can be viewed as “internalised judgmental equality”. In other words, if two terms
are strictly equal, than they are path equal::

  ≡ˢto≡ : {a : Level} {A : Set a} {x y : A} → x ≡ˢ y → x ≡ y
  ≡ˢto≡ refl = refl

The inverse does not hold. Agda rejects a map like ``≡to≡ˢ`` via the message::

  Panic: Pattern match failure in do expression at
  src/full/Agda/TypeChecking/Primitive/Cubical.hs:2304:7-21
  when checking the definition of ≡to≡ˢ

Just as the equality type, any usual type former can be defined again for strict types.
For example, the ``Σˢ``-type of dependent pairs is defined as follows::

  record Σˢ {a b} (A : SSet a) (B : A → SSet b) : SSet (a ⊔ b) where
    constructor _,ˢ_
    field
      fstˢ : A
      sndˢ : B fstˢ

When ``A : Set a`` and ``B : A → Set b``, we can show that ``Σˢ A B`` and ``Σ A B``
are isomorphic. The same is true for the type of dependent products and the unit type.

.. note::
   Currently, Agda does not support the elimination from fibrant types to non-fibrant
   types. However, there are some ways to circumvent this ban. See the issue `#5761
   <https://github.com/agda/agda/issues/5761>` for the details.
 
