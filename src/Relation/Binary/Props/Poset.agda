------------------------------------------------------------------------
-- The Agda standard library
--
-- Compatibility module. Pending for removal. Use
-- Relation.Binary.Properties.Poset instead.
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Props.Poset
         {p₁ p₂ p₃} (P : Poset p₁ p₂ p₃) where

open import Relation.Binary.Properties.Poset P public
