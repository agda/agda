------------------------------------------------------------------------
-- Some simple binary relations
------------------------------------------------------------------------

module Relation.Binary.Simple where

open import Relation.Binary
open import Data.Unit
open import Data.Empty

-- Constant relations.

Const : ∀ {a} → Set → Rel a
Const I = λ _ _ → I

-- The universally true relation.

Always : ∀ {a} → Rel a
Always = Const ⊤

-- The universally false relation.

Never : ∀ {a} → Rel a
Never = Const ⊥

-- Always is an equivalence.

Always-isEquivalence : ∀ {a} → IsEquivalence (Always {a})
Always-isEquivalence = record {}
