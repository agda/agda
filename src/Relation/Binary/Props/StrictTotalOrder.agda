------------------------------------------------------------------------
-- The Agda standard library
--
-- Compatibility module. Pending for removal. Use
-- Relation.Binary.Properties.StrictTotalOrder instead.
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Props.StrictTotalOrder
       {s₁ s₂ s₃} (STO : StrictTotalOrder s₁ s₂ s₃)
       where

open import Relation.Binary.Properties.StrictTotalOrder STO public
