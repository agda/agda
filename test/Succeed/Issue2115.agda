-- Andreas, 2016-07-26, issue 2215, reported by effectfully

data Term : Set where
  abs : Term → Term

Type = Term

f : Type → Term
f (abs b@(abs _)) = b

-- WAS: Panic: Pattern match failure in AsPatterns.conPattern
-- due to a missing reduce

-- Should work.
