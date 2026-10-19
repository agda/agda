-- Andreas, 2018-10-27, issue #3323, reported by Guillaume Brunerie
--
-- Mismatches between original and repeated parameter list
-- should not lead to internal errors.

{-# OPTIONS --erasure #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data T (b : Bool) : Set
data T (@0 b) where  -- Cannot change quantity
  c : Bool → T b

-- Should fail.
