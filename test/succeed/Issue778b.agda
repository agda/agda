-- {-# OPTIONS -v tc.term.exlam:100 -v extendedlambda:100 -v int2abs.reifyterm:100 -v tc.with:100 -v tc.mod.apply:100 #-}
module Issue778b (Param : Set) where

open import Issue778M Param

data D : (Nat → Nat) → Set where
  d : D pred → D pred

-- Ulf, 2013-11-11: With the fix to issue 59 that inlines with functions,
-- this no longer termination checks. The problem is having a termination
-- path going through a with-expression (the variable x in this case).
{-# NO_TERMINATION_CHECK #-}
test : (f : Nat → Nat) → D f → Nat
test .pred (d x) = bla
  where bla : Nat
        bla with x
        ... | (d y) = test pred y
