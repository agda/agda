
module _ where

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

data L : Nat → Set where
  nil  : L zero
  cons : ∀ n → L n → L (suc n)

pattern one = cons .zero nil
