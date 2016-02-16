------------------------------------------------------------------------
-- The Agda standard library
--
-- An equality postulate which evaluates
------------------------------------------------------------------------

module Relation.Binary.PropositionalEquality.TrustMe where

open import Relation.Binary.Core using (_≡_)

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
