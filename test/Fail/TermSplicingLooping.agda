open import Common.Prelude
open import Common.Reflection

module TermSplicingLooping where

mutual
  f : Set -> Set
  f = unquote (give (def (quote f) []))

-- Expected error:
--
-- Termination checking failed for the following functions:
--   f
-- Problematic calls:
--   f
