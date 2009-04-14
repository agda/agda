------------------------------------------------------------------------
-- Convenient syntax for equational reasoning
------------------------------------------------------------------------

-- Example use:

-- n*0≡0 : ∀ n → n * 0 ≡ 0
-- n*0≡0 zero    = refl
-- n*0≡0 (suc n) =
--   begin
--     suc n * 0
--   ≈⟨ byDef ⟩
--     n * 0 + 0
--   ≈⟨ n+0≡n _ ⟩
--     n * 0
--   ≈⟨ n*0≡0 n ⟩
--     0
--   ∎

open import Relation.Binary

module Relation.Binary.EqReasoning (s : Setoid) where

open Setoid s
import Relation.Binary.PreorderReasoning as PreR
open PreR preorder public
       renaming ( _∼⟨_⟩_  to _≈⟨_⟩_
                ; _≈⟨_⟩_  to _≡⟨_⟩_
                )
