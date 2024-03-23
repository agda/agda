-- Test for inductive-inductive data definitions
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.InductionInduction where

data Even : Set
data Odd : Set

data Even where
  s-even : Odd → Even
  z-even : Even

data Odd where
  s-odd : Even → Odd


f : Even → Even
g : Odd  → Even

f z-even = z-even
f (s-even odd) = g odd
g (s-odd even) = f even
