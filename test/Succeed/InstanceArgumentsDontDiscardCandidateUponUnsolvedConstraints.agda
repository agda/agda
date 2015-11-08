-- Andreas, 2012-09-15
module InstanceArgumentsDontDiscardCandidateUponUnsolvedConstraints where

import Common.Level

data ⊥ : Set where
record ⊤ : Set where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_≤_ : Nat → Nat → Set
zero    ≤ m       = ⊤
(suc n) ≤ zero    = ⊥
(suc n) ≤ (suc m) = n ≤ m

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)

lookup : {A : Set}{n : Nat} (m : Nat) {{m≤n : suc m ≤ n}} → Vec A n → A
lookup m {{()}} []
lookup zero     (a ∷ as) = a
lookup (suc m)  (a ∷ as) = lookup m as
-- the instance in the recursive call is only found
-- if the candiate  m≤n : suc m ≤ _n  is kept
-- until the blocking _n has been solved
