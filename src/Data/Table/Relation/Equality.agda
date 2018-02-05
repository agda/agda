------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise table equality
------------------------------------------------------------------------

module Data.Table.Relation.Equality where

open import Relation.Binary using (Setoid)
open import Data.Table.Base
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  as P using (_≡_; _→-setoid_)

setoid : ∀ {c p} → Setoid c p → ℕ → Setoid _ _
setoid S n = record
  { Carrier = Table Carrier n
  ; _≈_ = λ t t′ → ∀ i → lookup t i ≈ lookup t′ i
  ; isEquivalence = record
    { refl = λ i → refl
    ; sym = λ p → sym ∘ p
    ; trans = λ p q i → trans (p i) (q i)
    }
  }
  where open Setoid S

≡-setoid : ∀ {a} → Set a → ℕ → Setoid _ _
≡-setoid A = setoid (P.setoid A)

module _ {a} {A : Set a} {n} where
  open Setoid (≡-setoid A n) public
    using () renaming (_≈_ to _≗_)
