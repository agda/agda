------------------------------------------------------------------------
-- Convenient syntax for "equational reasoning" using a partial order
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Relation.Binary

module Relation.Binary.PartialOrderReasoning
         {p₁ p₂ p₃} (P : Poset p₁ p₂ p₃) where

open Poset P
import Relation.Binary.PreorderReasoning as PreR
open PreR preorder public renaming (_∼⟨_⟩_ to _≤⟨_⟩_)
