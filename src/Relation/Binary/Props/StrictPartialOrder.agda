------------------------------------------------------------------------
-- The Agda standard library
--
-- Compatibility module. Pending for removal. Use
-- Relation.Binary.Properties.StrictPartialOrder instead.
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Props.StrictPartialOrder
       {s₁ s₂ s₃} (SPO : StrictPartialOrder s₁ s₂ s₃) where

open import Relation.Binary.Properties.StrictPartialOrder SPO public
