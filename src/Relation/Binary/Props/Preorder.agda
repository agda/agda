------------------------------------------------------------------------
-- The Agda standard library
--
-- Compatibility module. Pending for removal. Use
-- Relation.Binary.Properties.Preorder instead.
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Props.Preorder
         {p₁ p₂ p₃} (P : Preorder p₁ p₂ p₃) where

open import Relation.Binary.Properties.Preorder P public
