{-# OPTIONS --safe --without-K #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

k : (Bool -> Bool) -> Bool
k g = g true

f : Bool -> Bool -> Bool -> Bool
f true x z = x
f y true = λ z -> false
f false false z = z
  module M where
    lem : k (f true true) ≡ false
    lem = refl

later : k (f true true) ≡ true
later = refl

data ⊥ : Set where

contra : {b : Bool} -> b ≡ true -> b ≡ false -> ⊥
contra refl ()

boom : ⊥
boom = contra later (M.lem true)
