..
  ::
  {-# OPTIONS --two-level --cumulativity #-}

  module language.two-level where

  open import Agda.Primitive

.. _two-level:

*********************
Two-Level Type Theory
*********************

Basics
------

Two-level type theory (2LTT) refers to versions of Martin-Löf type
theory that combine two type theories: one "inner" level that is
potentially a homotopy type theory or cubical type theory, which may
include univalent universes and higher inductive types, and a second
"outer" level that validates uniqueness of identity proofs.

Since version 2.6.2, Agda enables 2LTT with the ``--two-level`` flag.
The two levels are distinguished with two hierarchies of universes:
the usual universes ``Set`` for the inner level, and a new hierarchy
of universes denoted ``SSet`` (for "strict sets") for the outer level.

.. note::
   The types in ``SSet`` have various names in the literature. They
   are called `non-fibrant types` in `HTS (2017)
   <https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/HTS.pdf>`_,
   `outer types` in `2LTT (2017)
   <https://arxiv.org/abs/1705.03307>`_, and `exo-types` in
   `UP (2021) <https://arxiv.org/abs/2102.06275>`_.  Similarly,
   these references refer to the types in ``Set`` as `fibrant types`,
   `inner types`, and `types`, respectively.

Function-types belong to ``Set`` if both their domain and codomain do,
and to ``SSet`` otherwise.  Records and datatypes can always be
declared to belong to ``SSet``, and can be declared to belong to
``Set`` instead if all their inputs belong to ``Set``.  In particular,
any type in ``Set`` has an isomorphic copy in ``SSet`` defined as a
trivial record::

  record c (A : Set) : SSet where
    constructor ↑
    field
      ↓ : A

  open c

The main differences between the two levels are that, firstly,
homotopical flags such as ``--without-K`` and ``--cubical`` apply only
to the ``Set`` level (the ``SSet`` level is never homotopical); and
secondly, datatypes belonging to the inner level cannot be
pattern-matched on when the motive belongs to the outer level (this is
necessary to maintain the previous distinction).

As a primary example, we can define separate inductive equality types
for both levels::

  infix 4 _≡ˢ_ _≡_

  data _≡ˢ_ {a} {A : SSet a} (x : A) : A → SSet a where
    reflˢ : x ≡ˢ x

  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x

With these definitions, we can prove uniqueness of identity proofs for
the strict equality even if ``--without-K`` or ``--cubical`` is
enabled::

  UIP : {a : Level} {A : SSet a} {x y : A} (p q : x ≡ˢ y) → p ≡ˢ q
  UIP reflˢ reflˢ = reflˢ

We can also prove that strictly equal elements are also non-strictly equal::

  ≡ˢ-to-≡ : {A : Set} {x y : c A} → (x ≡ˢ y) → (↓ x ≡ ↓ y)
  ≡ˢ-to-≡ reflˢ = refl

The opposite implication, however, fails because, as noted above, we
cannot pattern-match against a datatype in ``Set`` when the motive
lies in ``SSet``.  Similarly, we can map from the strict natural
numbers into the ordinary ones::

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  data ℕˢ : SSet where
    zeroˢ : ℕˢ
    succˢ : ℕˢ → ℕˢ

  ℕˢ-to-ℕ : ℕˢ → ℕ
  ℕˢ-to-ℕ zeroˢ = zero
  ℕˢ-to-ℕ (succˢ n) = succ (ℕˢ-to-ℕ n)

but not vice versa.
(Agda does currently allow mapping from the empty ``SSet`` to the empty ``Set``,
but this feature is `disputed <https://github.com/agda/agda/issues/5761#issuecomment-1154239427>`_.)

If the ``--two-level`` flag is combined with ``--cumulativity``, then
each universe ``Set a`` becomes a subtype of ``SSet a``.  In this case
we can instead define the coercion ``c`` to be the identity function::

  c' : Set → SSet
  c' A = A

and replace the coercions ``↑`` and ``↓`` with the identity function.
However, this combination currently allows some functions to be
defined that shouldn't be allowed; see `Agda issue #5761
<https://github.com/agda/agda/issues/5761>`_ for details.
