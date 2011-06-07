open import Common.Prelude

module TestHarness where

record ⊤ : Set where

data ⊥ : Set where

T : Bool → Set
T true  = ⊤
T false = ⊥

infixr 4 _,_

data Asserts : Set where
  ε : Asserts
  _,_ : Asserts → Asserts → Asserts
  assert : (b : Bool) → {b✓ : T b} → String → Asserts

Tests : Set
Tests = ⊤ → Asserts
