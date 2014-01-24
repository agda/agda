------------------------------------------------------------------------
-- The Agda standard library
--
-- Compatibility module. Pending for removal. Use
-- Relation.Binary.Properties.DecTotalOrder instead.
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Props.DecTotalOrder
         {d₁ d₂ d₃} (DT : DecTotalOrder d₁ d₂ d₃) where

open import Relation.Binary.Properties.DecTotalOrder DT public
