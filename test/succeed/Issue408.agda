
module Issue408 where

open import Common.Prelude
open import Common.Equality

-- Agda should prefer to split on an argument that covers

data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc  : {n : Nat} → Fin n → Fin (suc n)

wk : {n : Nat} → Fin n → Fin (suc n)
wk zero = zero
wk (suc n) = suc (wk n)

predFin : (n : Nat) → Fin n → Fin n
predFin (suc n) zero    = zero
predFin (suc n) (suc i) = wk i
-- predFin should be covering

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : {n : Nat} (x : A) (xs : Vec A n) → Vec A (suc n)

_!!_ : {A : Set}{n : Nat} → Vec A n → Fin n → A
_!!_ (x ∷ xs) zero    = x
_!!_ (x ∷ xs) (suc i) = xs !! i
-- should be covering, no need for absurd clause
