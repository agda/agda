-- Andreas, 2024-03-07, issue #2829.
-- Allow instance variables in pattern synonym lhss
-- if they are in instance position on the rhs.

module _ where

  data D : Set where
    c : {{D}} → D

  pattern p {{d}} = c {{d}}  -- Should be accepted.

  f : D → D
  f (p {{d = x}}) = x

  g : D → D
  g c = c

  h : D → D
  h p = c

  i : D → D
  i p = p  -- Should solve.

  j : D → D
  j (p {{d}}) = p {{d = d}}
