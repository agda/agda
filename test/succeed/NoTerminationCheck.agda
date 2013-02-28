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

-- Skipping an old-style mutual block (placed before)

{-# NO_TERMINATION_CHECK #-}
mutual
  c : A
  c = d

  d : A
  d = c

-- Skipping an old-style mutual block (placed within)

mutual
  {-# NO_TERMINATION_CHECK #-}
  c1 : A
  c1 = d1

  d1 : A
  d1 = c1

mutual
  c2 : A
  {-# NO_TERMINATION_CHECK #-}
  c2 = d2

  d2 : A
  d2 = c2

mutual
  c3 : A
  c3 = d3

  {-# NO_TERMINATION_CHECK #-}
  d3 : A
  d3 = c3

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

