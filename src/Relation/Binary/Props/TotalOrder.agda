------------------------------------------------------------------------
-- The Agda standard library
--
-- Compatibility module. Pending for removal. Use
-- Relation.Binary.Properties.TotalOrder instead.
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Props.TotalOrder
         {t₁ t₂ t₃} (T : TotalOrder t₁ t₂ t₃) where

open import Relation.Binary.Properties.TotalOrder T public
