------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for equational reasoning
------------------------------------------------------------------------

-- Example use:

-- n*0≡0 : ∀ n → n * 0 ≡ 0
-- n*0≡0 zero    = refl
-- n*0≡0 (suc n) =
--   begin
--     suc n * 0
--   ≈⟨ refl ⟩
--     n * 0 + 0
--   ≈⟨ ... ⟩
--     n * 0
--   ≈⟨ n*0≡0 n ⟩
--     0
--   ∎

-- Module ≡-Reasoning in Relation.Binary.PropositionalEquality
-- is recommended for equational reasoning when the underlying equality is
-- Relation.Binary.PropositionalEquality._≡_.

open import Relation.Binary

module Relation.Binary.EqReasoning {s₁ s₂} (S : Setoid s₁ s₂) where

open Setoid S
import Relation.Binary.PreorderReasoning as PreR
open PreR preorder public
       renaming ( _∼⟨_⟩_  to _≈⟨_⟩_
                ; _≈⟨_⟩_  to _≡⟨_⟩_
                ; _≈⟨⟩_  to _≡⟨⟩_
                )
