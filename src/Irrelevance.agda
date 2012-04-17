------------------------------------------------------------------------
-- The Agda standard library
--
-- The irrelevance axiom
------------------------------------------------------------------------

module Irrelevance where

import Level

------------------------------------------------------------------------
-- The irrelevance axiom

-- There is no guarantee that this axiom is sound. Use it at your own
-- risk.

postulate
  .irrelevance-axiom : ∀ {a} {A : Set a} → .A → A

{-# BUILTIN IRRAXIOM irrelevance-axiom #-}
