------------------------------------------------------------------------
-- Some properties imply others
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary.Consequences.

module Relation.Binary.Consequences.Core where

open import Relation.Binary.Core
open import Data.Product

subst⟶resp₂
  :  forall {a ∼} -> (P : Rel a)
  -> Substitutive ∼
  -> ∼ Respects₂ P
subst⟶resp₂ {∼ = ∼} P subst =
  (\{x _ _} y'∼y Pxy' -> subst (P x)         y'∼y Pxy') ,
  (\{y _ _} x'∼x Px'y -> subst (\x -> P x y) x'∼x Px'y)
