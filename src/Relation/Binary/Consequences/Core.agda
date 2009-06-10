------------------------------------------------------------------------
-- Some properties imply others
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary.Consequences.

module Relation.Binary.Consequences.Core where

open import Relation.Binary.Core
open import Data.Product

subst⟶resp₂ : ∀ {a ∼} (P : Rel a) → Substitutive ∼ → P Respects₂ ∼
subst⟶resp₂ {∼ = ∼} P subst =
  (λ {x _ _} y'∼y Pxy' → subst (P x)         y'∼y Pxy') ,
  (λ {y _ _} x'∼x Px'y → subst (λ x → P x y) x'∼x Px'y)
