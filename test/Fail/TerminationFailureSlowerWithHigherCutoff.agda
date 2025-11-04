-- Andreas, 2025-11-01
-- Example that was slow with high termination-depth.
-- Andreas, 2025-11-04
-- Again slow, because heuristics
-- "Any increase in the diagonal of a loop can be strengthened to infinite increase"
-- is moot.

{-# OPTIONS --termination-depth=42 #-}  -- don't make this too high!

-- {-# OPTIONS --profile=internal #-}
-- {-# OPTIONS -v debug.time:100 #-}
-- {-# OPTIONS -v term:3 #-}
-- {-# OPTIONS -v term.matrices:40 #-}

data N : Set where
  s_ : N → N
  zero : N

-- Start timer
dummy : N → N
dummy (s n) = dummy n
dummy zero = zero

mutual
  -- If we put more constructors here, the LHS checker becomes the bottleneck.
  f : N → N
  f (
   s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s
   s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s
   s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s
   s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s
   s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s
   s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s
   s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s
   s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s
   s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s
   s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s s
   x) = g x x
  f x = zero

  g : N → N → N
  g (s x) y = g x (s y)
  g zero  y = f y
