
module Issue254 where

data Unit : Set where
  * : Unit

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Vec : Nat → Set where
  cons : ∀ n → Vec (suc n)

remove : ∀ n → Nat → Vec (suc n) → Unit
remove n x (cons .n) with *
remove n x (cons .n) | * = {!!}
