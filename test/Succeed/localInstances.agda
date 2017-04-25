module localInstances where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool
open import Common.String
open import Common.List

record Eq (A : Set) : Set where
  field eq : A → A → Bool

strlen : String → ℕ
strlen s = length (stringToList s)

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

open Eq {{...}}

instance
  eqℕ : Eq ℕ
  eqℕ = record { eq = λ x x' → x == x' }

eqString₁ : String → String → Bool
eqString₁ s₁ s₂ = strEq s₁ s₂

eqString₂ : String → String → Bool
eqString₂ s₁ s₂ = eq (strlen s₁) (strlen s₂)

testWhere : Bool → Bool
testWhere lengthEq = if eq "abcd" "dcba" then false else true
  where
    instance
      eqLocal : Eq String
      eqLocal = record { eq = if lengthEq then eqString₂ else eqString₁ }

testLet : Bool → Bool
testLet lengthEq =
  let instance
        eqLocal : Eq String
        eqLocal = record { eq = if lengthEq then eqString₂ else eqString₁ }
  in if eq "abcd" "dcba" then false else true

test1 : Bool
test1 = testWhere true

test2 : Bool
test2 = testLet true
