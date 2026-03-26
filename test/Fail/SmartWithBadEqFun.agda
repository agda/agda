{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite


not : Bool → Bool
not true  = false
not false = true

id : Bool → Bool
id true  = true
id false = false

f : not ≡ id → Nat
f p rewrite p = 42
