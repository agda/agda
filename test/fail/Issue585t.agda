-- Andreas, 2012-03-13
module Issue585t where

postulate
  A : Set
  a : A    -- just so that A is not empty and the constraints are solvable
           -- however, Agda picks the wrong solution

data B : Set where
  inn : A -> B

out : B -> A
out (inn a) = a

postulate
  P : (y : A) (z : B) → Set
  p : (x : B) → P (out x) x

mutual
  d : B
  d = inn _           -- Y

  g : P (out d) d
  g = p _             -- X

-- Agda previously solved  d = inn (out d)
--
-- out X = out d = out (inn Y) = Y
-- X = d
--
-- Now this does not pass the occurs check, so unsolved metas should remain.
