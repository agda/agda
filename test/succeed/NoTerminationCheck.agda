-- 2012-03-08 Andreas
module NoTerminationCheck where

postulate A : Set

-- Skipping a single definition: before type signature

{-# NO_TERMINATION_CHECK #-}
a : A
a = a

-- Skipping a single definition: before first clause

b : A
{-# NO_TERMINATION_CHECK #-}
b = b

-- Skipping an old-style mutual block

{-# NO_TERMINATION_CHECK #-}
mutual
  c : A
  c = d

  d : A
  d = c


-- Skipping a new-style mutual block

{-# NO_TERMINATION_CHECK #-}
e : A
f : A

e = f
f = e

-- Skipping a new-style mutual block, variant 2

g : A
{-# NO_TERMINATION_CHECK #-}
h : A

g = h
h = g


-- Skipping a new-style mutual block, variant 4

i : A
j : A

i = j
{-# NO_TERMINATION_CHECK #-}
j = i

private
  {-# NO_TERMINATION_CHECK #-}
  k : A
  k = k

abstract
  {-# NO_TERMINATION_CHECK #-}
  l : A
  l = l

