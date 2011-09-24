------------------------------------------------------------------------
-- The Agda standard library
--
-- Some simple binary relations
------------------------------------------------------------------------

module Relation.Binary.Simple where

open import Relation.Binary
open import Data.Unit
open import Data.Empty
open import Level

-- Constant relations.

Const : ∀ {a b c} {A : Set a} {B : Set b} → Set c → REL A B c
Const I = λ _ _ → I

-- The universally true relation.

Always : ∀ {a ℓ} {A : Set a} → Rel A ℓ
Always = Const (Lift ⊤)

Always-setoid : ∀ {a ℓ} (A : Set a) → Setoid a ℓ
Always-setoid A = record
  { Carrier       = A
  ; _≈_           = Always
  ; isEquivalence = record {}
  }

-- The universally false relation.

Never : ∀ {a ℓ} {A : Set a} → Rel A ℓ
Never = Const (Lift ⊥)
