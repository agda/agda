{-# OPTIONS --polarity --no-occurrence-analysis #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit

data _×_ (@++ A B : Set) : Set where
  _,_ : A → B → A × B

Vec : @++ Set → Nat → Set
Vec A zero    = ⊤
Vec A (suc n) = A × Vec A n

data D : Set where
  c : ∀ n → Vec D n → D

F : Bool → @unused Set → Set
F true  _ = Bool
F false _ = ⊤

_ : {b : Bool} → F b Bool ≡ F b ⊤
_ = refl
