-- 2012-03-08 Andreas
-- 2014-09-09 Andreas, use NON_TERMINATING or TERMINATING instead

postulate A : Set

-- Skipping a single definition: before type signature

{-# NON_TERMINATING #-}
a : A
a = a

-- Skipping a single definition: before first clause

b : A
{-# NON_TERMINATING #-}
b = b

-- Skipping an old-style mutual block (placed before)

{-# NON_TERMINATING #-}
mutual
  c : A
  c = d

  d : A
  d = c

-- Skipping an old-style mutual block (placed within)

mutual
  {-# TERMINATING #-}  -- It's a lie!!
  c1 : A
  c1 = d1

  d1 : A
  d1 = c1

mutual
  c2 : A
  {-# NON_TERMINATING #-}
  c2 = d2

  d2 : A
  d2 = c2

mutual
  c3 : A
  c3 = d3

  {-# NON_TERMINATING #-}
  d3 : A
  d3 = c3

-- Skipping a new-style mutual block

{-# NON_TERMINATING #-}
e : A
f : A

e = f
f = e

-- Skipping a new-style mutual block, variant 2

g : A
{-# TERMINATING #-}  -- Beware of lies!!
h : A

g = h
h = g


-- Skipping a new-style mutual block, variant 4

i : A
j : A

i = j
{-# NON_TERMINATING #-}
j = i

private
  {-# NON_TERMINATING #-}
  k : A
  k = k

abstract
  {-# NON_TERMINATING #-}
  l : A
  l = l

