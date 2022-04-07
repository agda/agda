{-# OPTIONS --cubical-compatible #-}

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data ⊥ : Set where

record Σ {a} {b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

no : _≡_ {A = Σ Set (λ X → X)} (Nat , 0) (Nat , 1) → ⊥
no ()
