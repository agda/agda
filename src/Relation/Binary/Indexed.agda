------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed binary relations
------------------------------------------------------------------------

module Relation.Binary.Indexed where

import Relation.Binary as B

open import Relation.Binary.Indexed.Core public

-- By "instantiating" an indexed setoid one gets an ordinary setoid.

_at_ : ∀ {i s₁ s₂} {I : Set i} → Setoid I s₁ s₂ → I → B.Setoid _ _
S at i = record
  { Carrier       = S.Carrier i
  ; _≈_           = S._≈_
  ; isEquivalence = record
    { refl  = S.refl
    ; sym   = S.sym
    ; trans = S.trans
    }
  } where module S = Setoid S

------------------------------------------------------------------------
-- Simple properties of indexed binary relations

-- Generalised implication.

infixr 4 _=[_]⇒_

_=[_]⇒_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : A → Set b} →
          B.Rel A ℓ₁ → ((x : A) → B x) → Rel B ℓ₂ → Set _
P =[ f ]⇒ Q = ∀ {i j} → P i j → Q (f i) (f j)
