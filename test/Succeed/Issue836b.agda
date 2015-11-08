-- Andreas, 2013-05-02 This ain't a bug, it is a feature.
-- {-# OPTIONS -v scope.name:10 #-}
module _ where

open import Common.Equality

module M where

  record R' : Set₁ where
    field
      X : Set

open M renaming (R' to R)

X : R → Set
X = R.X

-- Nisse:
-- The open directive did not mention the /module/ R, so (I think
-- that) the code above should be rejected.

-- Andreas:
-- NO, it is a feature that projections can also be accessed via
-- the record /type/.

-- Ulf:
-- According to the suggestion in 836, if you rename the module explicitly
-- the code above breaks (test/fail/Issue836.agda).
