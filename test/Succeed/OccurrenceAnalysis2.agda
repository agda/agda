{-# OPTIONS --occurrence-analysis #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Unit

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

Vec : Set → Nat → Set
Vec A zero    = ⊤
Vec A (suc n) = A × Vec A n

data D : Set where
  c : ∀ n → Vec D n → D
