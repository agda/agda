
module Issue413 where

data Bool : Set where

data ℕ : Set where
  zero : ℕ

data Type : (A : Set) → Set where
   isBool : Type Bool
   isℕ    : Type ℕ

g : (A : Set) → Type A → Type A → ℕ
g .Bool isBool isBool = zero
