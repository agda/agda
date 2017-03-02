-- Andreas, issue #2482, reported by Guillaume Allais
-- Internal error because of wrong value for
-- number of parameters for data type.

-- {-# OPTIONS -v tc.data.sort:50 #-}
-- {-# OPTIONS -v tc.term.con:50 #-}

data D {b} (B : Set b) : Set b

-- This used to falsely compute the number of parameters to 1

data D B where
  c : B → D B

-- ... leading to a violated invariant when applying the constructor.

test : ∀ {B : Set} (b : B) → D B
test b = c b

-- n  = npars  = conPars (c)
-- n' = npars' = getNumberOfParameters (D)
-- should be the same
