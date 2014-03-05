-- 2014-03-05 Andreas, issue reported by James

-- {-# OPTIONS -v tc.with.strip:60 -v:impossible:10 #-}

data Nat : Set where
  zero : Nat

pattern pzero = zero

f : Nat → Nat
f pzero with pzero
f pzero | pzero = pzero

-- ERROR WAS:
-- With clause pattern pzero is not an instance of its parent pattern
-- when checking that the clause
-- f pzero with pzero
-- f pzero | pzero = pzero
-- has type Nat → Nat
