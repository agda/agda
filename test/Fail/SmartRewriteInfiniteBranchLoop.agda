{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat

data ⊥ : Set where

data Branch : Set where
  branch : (Nat → Branch) → Branch

rec : Branch → ⊥
rec (branch f) = rec (f 0)

foo : (f : Nat → Branch) (bad : ⊥) → f 0 ≡ branch f → rec (f 0) ≡ bad
foo f bad p rewrite p = {!!}
--  rewrite p = refl
