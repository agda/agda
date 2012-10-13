
module Issue408 where

open import Common.Prelude
open import Common.Equality

-- 1. Agda should prefer to split on an argument that covers

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
(x ∷ xs) !! zero    = x
(x ∷ xs) !! (suc i) = xs !! i
-- should be covering, no need for absurd clause

test!!1 : ∀ {A}{n} (x : A) (xs : Vec A n) →   (x ∷ xs) !! zero    ≡ x
test!!1 x xs = refl

test!!2 : ∀ {A}{n} (x : A) (xs : Vec A n) i → (x ∷ xs) !! (suc i) ≡ xs !! i
test!!2 x xs i = refl

-- 2. Agda should prefer  to split on an argument that has only
-- constructor patterns.  For max below, split on 2nd, then on 1st.

max : Nat → Nat → Nat
max (suc n) (suc m) = suc (max n m)
max 0       (suc m) = suc m
max n        0      = n

testmax1 : {n m : Nat} → max (suc n) (suc m) ≡ suc (max n m)
testmax1 = refl

testmax2 : {m : Nat} → max 0 (suc m) ≡ suc m
testmax2 = refl

{- DOES NOT WORK YET
testmax3 : {n : Nat} → max n 0 ≡ n
testmax3 = refl
-- equation should hold definitionally
-}
