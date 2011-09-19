------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on nullary relations (like negation and decidability)
------------------------------------------------------------------------

-- Some operations on/properties of nullary relations, i.e. sets.

module Relation.Nullary where

import Relation.Nullary.Core as Core

------------------------------------------------------------------------
-- Negation

open Core public using (¬_)

------------------------------------------------------------------------
-- Decidable relations

open Core public using (Dec; yes; no)
