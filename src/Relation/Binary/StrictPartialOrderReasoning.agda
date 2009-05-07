------------------------------------------------------------------------
-- Convenient syntax for "equational reasoning" using a strict partial
-- order
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.StrictPartialOrderReasoning
         (p : StrictPartialOrder) where

import Relation.Binary.PreorderReasoning as PreR
import Relation.Binary.Props.StrictPartialOrder as SPO
open PreR (SPO.preorder p) public renaming (_∼⟨_⟩_ to _<⟨_⟩_)
