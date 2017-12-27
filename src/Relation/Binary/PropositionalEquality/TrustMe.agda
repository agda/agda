------------------------------------------------------------------------
-- The Agda standard library
--
-- An equality postulate which evaluates
------------------------------------------------------------------------

module Relation.Binary.PropositionalEquality.TrustMe where

open import Relation.Binary.Core using (_≡_; refl)

open import Agda.Builtin.TrustMe

-- trustMe {x = x} {y = y} evaluates to refl if x and y are
-- definitionally equal.
--
-- For an example of the use of trustMe, see Data.String._≟_.

trustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y
trustMe = primTrustMe

-- "Erases" a proof. The original proof is not inspected. The
-- resulting proof reduces to refl if the two sides are definitionally
-- equal. Note that checking for definitional equality can be slow.

erase : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
erase _ = trustMe

-- A "postulate with a reduction": postulate[ a ↦ b ] a evaluates to b,
-- while postulate[ a ↦ b ] a' gets stuck if a' is not definitionally
-- equal to a. This can be used to define a postulate of type (x : A) → B x
-- by only specifying the behaviour at B t for some t : A. Introduced in
--
--   Alan Jeffrey, Univalence via Agda's primTrustMe again
--   23 January 2015
--   https://lists.chalmers.se/pipermail/agda/2015/007418.html

postulate[_↦_] : ∀ {a b} {A : Set a}{B : A → Set b} →
                  (t : A) → B t → (x : A) → B x
postulate[ a ↦ b ] a' with trustMe {x = a} {a'}
postulate[ a ↦ b ] .a | refl = b
