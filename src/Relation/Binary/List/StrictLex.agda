------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists
--
-- This module is DEPRECATED. Please use Data.List.Relation.Lex.Strict
-- directly.
------------------------------------------------------------------------

-- The definition of lexicographic ordering used here is suitable if
-- the argument order is a strict partial order. The lexicographic
-- ordering itself can be either strict or non-strict, depending on
-- the value of a parameter.

module Relation.Binary.List.StrictLex where

open import Data.List.Relation.Lex.Core public
open import Data.List.Relation.Lex.Strict public
  hiding (base; halt; this; next; ¬≤-this; ¬≤-next)
