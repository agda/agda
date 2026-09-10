-- Erased matches for non-dependent, single-constructor data types can
-- be disallowed.

{-# OPTIONS --erasure --erased-matches=none #-}

data Unit : Set where
  unit : Unit

f : @0 Unit → Unit
f unit = unit
