------------------------------------------------------------------------
-- The Agda standard library
--
-- An equality postulate which evaluates
------------------------------------------------------------------------

module Relation.Binary.PropositionalEquality.TrustMe where

open import Relation.Binary.PropositionalEquality

private
 primitive
   primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

-- trustMe {x = x} {y = y} evaluates to refl if x and y are
-- definitionally equal.
--
-- For an example of the use of trustMe, see Data.String._≟_.

trustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y
trustMe = primTrustMe
