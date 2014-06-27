-- Andreas, 2014-06-27
-- {-# OPTIONS -v tc.lhs:40 #-}
{-# OPTIONS --copatterns #-}

record Coind : Set where
  coinductive
  field ind : Coind

open Coind

loop : Set -> Coind
ind A (loop B) = ind (loop A)

-- WAS: Internal error.

-- NOW: Proper error.
-- Cannot eliminate type Coind with pattern ind A (did you supply too many arguments?)
-- when checking that the clause ind A (loop B) = ind (loop A) has
-- type Set → Coind
