------------------------------------------------------------------------
-- Some simple binary relations
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Simple where

open import Relation.Binary
open import Data.Unit
open import Data.Empty

-- Constant relations.

Const : ∀ {a b} {A : Set a} → Set b → REL A b
Const I = λ _ _ → I

-- The universally true relation.

Always : ∀ {a} {A : Set a} → Rel A
Always = Const ⊤

-- The universally false relation.

Never : ∀ {a} {A : Set a} → Rel A
Never = Const ⊥

-- Always is an equivalence.

Always-isEquivalence : ∀ {a} {A : Set a} →
                       IsEquivalence (Always {A = A})
Always-isEquivalence = record {}
