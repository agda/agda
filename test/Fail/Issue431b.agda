{-# OPTIONS --inversion-max-depth=10 #-}

open import Agda.Builtin.Nat

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

F : Nat → Set
F zero    = Nat
F (suc n) = Nat × F n

f : (n : Nat) → F n
f zero    = zero
f (suc n) = n , f n

mutual

  n : Nat
  n = _

  test : F n
  test = f (suc n)
