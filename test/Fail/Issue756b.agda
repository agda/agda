
module Issue756b where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data T : (Nat → Nat) → Set where
  idId : T (λ { zero → zero; (suc n) → suc n })

bad : ∀ f → T f → Nat
bad .(λ { zero → zero ; (suc n) → suc n }) idId = zero

-- Expected error:
-- Pattern lambdas are not allowed in dot patterns
