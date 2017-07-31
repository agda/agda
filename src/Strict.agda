------------------------------------------------------------------------
-- The Agda standard library
--
-- Strictness combinators
------------------------------------------------------------------------

module Strict where

open import Level
open import Agda.Builtin.Equality

open import Agda.Builtin.Strict
     renaming ( primForce to force
              ; primForceLemma to force-≡) public

-- Derived combinators
module _ {ℓ ℓ′ : Level} {A : Set ℓ} {B : Set ℓ′} where

  force′ : A → (A → B) → B
  force′ = force

  force′-≡ : (a : A) (f : A → B) → force′ a f ≡ f a
  force′-≡ = force-≡

  seq : A → B → B
  seq a b = force a (λ _ → b)

  seq-≡ : (a : A) (b : B) → seq a b ≡ b
  seq-≡ a b = force-≡ a (λ _ → b)
