------------------------------------------------------------------------
-- An equality postulate which evaluates
------------------------------------------------------------------------

module Relation.Binary.PropositionalEquality.TrustMe where

open import Relation.Binary.PropositionalEquality

private
 primitive
   primTrustMe : {A : Set}{a b : A} → a ≡ b

-- trustMe {a = x} {b = y} evaluates to refl if x and y are
-- definitionally equal.
--
-- For an example of the use of trustMe, see Data.String._≟_.

trustMe : {A : Set}{a b : A} → a ≡ b
trustMe = primTrustMe
