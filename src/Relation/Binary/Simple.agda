------------------------------------------------------------------------
-- Some simple binary relations
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Simple where

open import Relation.Binary
open import Data.Unit
open import Data.Empty
open import Level

-- Constant relations.

Const : ∀ {a b c} {A : Set a} {B : Set b} → Set c → REL A B c
Const I = λ _ _ → I

-- The universally true relation.

Always : ∀ {a} {A : Set a} → Rel A zero
Always = Const ⊤

Always-setoid : ∀ {a} (A : Set a) → Setoid _ _
Always-setoid A = record
  { Carrier       = A
  ; _≈_           = Always
  ; isEquivalence = record {}
  }

-- The universally false relation.

Never : ∀ {a} {A : Set a} → Rel A zero
Never = Const ⊥
