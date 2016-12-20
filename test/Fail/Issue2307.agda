-- Andreas, 2016-12-03, issue 2307
-- preserve record (vs. constructor) in internal syntax

open import Common.Equality

postulate
  A : Set
  a : A

record R : Set where
  constructor c
  field f : A
open R

postulate
  r : R
  g h : R → R

fail1 : g (c a) ≡ h (record{ f = a })
fail1 = refl

-- ERROR:     g (c a) != h (c a)
-- Expected:  g (c a) != h (record{ f = a })
