
module _ where

open import Agda.Builtin.Nat renaming (Nat to Nombre)
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.Reflection

check₁ : primShowQName (quote Nombre) ≡ "Agda.Builtin.Nat.Nat"
check₁ = refl

check₂ : primShowQName (quote Agda.Builtin.Nat.Nat) ≡ "Agda.Builtin.Nat.Nat"
check₂ = refl
