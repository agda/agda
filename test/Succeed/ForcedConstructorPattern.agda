{-# OPTIONS -v tc.cover.splittree:50 #-}

open import Agda.Builtin.Nat

data Vec (A : Set) : Nat → Set where
  nil  : Vec A zero
  cons : (n : Nat) → A → Vec A n → Vec A (suc n)

append : {A : Set} (m n : Nat) → Vec A m → Vec A n → Vec A (m + n)
append .zero    n nil            ys = ys
append (.suc m) n (cons .m x xs) ys = cons (m + n) x (append m n xs ys)

open import Agda.Builtin.Equality

data _×_ (A B : Set) : Set where
  pair : A → B → A × B

test : (p q : Nat × Nat) → p ≡ q → Set₁
test (.(pair x) y) (pair x .y) refl = Set
