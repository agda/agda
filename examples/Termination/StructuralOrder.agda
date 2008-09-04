-- some examples for structural order in the termination checker

module StructuralOrder where

data Nat : Set where
   zero : Nat
   succ : Nat -> Nat

-- c t > t  for any term t
-- e.g., succ (succ y) > succ y
plus : Nat -> Nat -> Nat
plus x (succ (succ y)) = succ (plus x (succ y))
plus x (succ zero) = succ x
plus x zero        = x

-- constructor names do not matter
-- c (c' t) > c'' t
-- e.g. c0 (c1 x) > c0 x
--      c0 (c0 x) > c1 x

-- Actually constructor names does matter until the non-mattering is
-- implemented properly.

{- TEMPORARILY REMOVED by Ulf since there are problems with the constructor-name ignoring
data Bin : Set where
  eps : Bin
  c0  : Bin -> Bin
  c1  : Bin -> Bin

foo : Bin -> Nat
foo eps = zero
foo (c0 eps) = zero
foo (c0 (c1 x)) = succ (foo (c0 x))
foo (c0 (c0 x)) = succ (foo (c1 x))
foo (c1 x)      = succ (foo x)
-}
