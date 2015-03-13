
module _ where

record ⊤ : Set where
  instance
    constructor tt

data Nat : Set where
  suc  : Nat → Nat

NZ : Nat → Set
NZ (suc _) = ⊤

postulate
  A : ∀ n → {{_ : NZ n}} → Set

B : ∀ n (nz : NZ n) → Set
B (suc n) nz = A (suc n)
