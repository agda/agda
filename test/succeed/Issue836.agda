-- Andreas, 2013-05-02 This ain't a bug, it is a feature.
-- {-# OPTIONS -v scope.name:10 #-}
module Issue836 where

open import Common.Equality

module M where

  record R : Set₁ where
    field
      X : Set

open M using (R)

X : R → Set
X = R.X

-- The open directive did not mention the /module/ R, so (I think
-- that) the code above should be rejected.

-- NO, it is a feature that projections can also be accessed via
-- the record /type/.

-- The following directive is (and should be) rejected:

-- open R

-- Bug.agda:19,6-7
-- No such module R
-- when scope checking the declaration
--   open R

module N where

  data D : Set₁ where
    c : Set → D

open N using (D) renaming (module D to MD)

twoWaysToQualify : D.c ≡ MD.c
twoWaysToQualify = refl

