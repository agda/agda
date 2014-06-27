-- Andreas, 2014-06-27 test case by Ulf
-- {-# OPTIONS -v tc.lhs:40 #-}
{-# OPTIONS --copatterns #-}

record Coind : Set where
  coinductive
  field ind : Coind

open Coind

loop : Set -> Coind
ind A loop = ind (loop A)

-- WAS: Internal error.

-- NOW: Proper error.
-- Ill-formed projection pattern ind A
-- when checking that the clause ind A loop = ind (loop A) has type
-- Set → Coind
