------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of relations to vectors
--
-- This module is DEPRECATED.
-- Please use Data.Vec.Relation.InductivePointwise
-- and Data.Vec.Relation.ExtensionalPointwise directly.
------------------------------------------------------------------------

module Relation.Binary.Vec.Pointwise where

open import Data.Vec.Relation.InductivePointwise public
  hiding (head; tail)
open import Data.Vec.Relation.ExtensionalPointwise public
  using (head; tail) renaming (Pointwise to Pointwise′)
