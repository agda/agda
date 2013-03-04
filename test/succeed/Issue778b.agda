{-# OPTIONS -v tc.term.exlam:100 -v extendedlambda:100 -v int2abs.reifyterm:100 -v tc.with:100 -v tc.mod.apply:100 #-}
module Issue778b (Param : Set) where

open import Issue778M Param

data D : (Nat → Nat) → Set where
  d : D pred → D pred

test : (f : Nat → Nat) → D f → Nat
test .pred (d x) = bla
  where bla : Nat
        bla with x
        ... | (d y) = test pred y

