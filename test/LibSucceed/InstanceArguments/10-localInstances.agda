module InstanceArguments.10-localInstances where

import Data.Empty as E
open import Data.String using (String; toList; _≟_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ) renaming (_≟_ to _ℕ≟_)
import Data.List as List
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function using (_on_; _∘_)

record Eq (A : Set) : Set where
  field eq : A → A → Bool

length : String → ℕ
length = List.length ∘ toList

open Eq {{...}}

instance
  eqℕ : Eq ℕ
  eqℕ = record { eq = λ x x' → ⌊ x ℕ≟ x' ⌋ }

eqString₁ : String → String → Bool
eqString₁ s₁ s₂ = ⌊ s₁ ≟ s₂ ⌋

eqString₂ : String → String → Bool
eqString₂ = eq on length

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
