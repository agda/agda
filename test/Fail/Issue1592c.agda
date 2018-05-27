-- Andreas, 2015-06-29 fixed handling of projections in positivity checker

-- {-# OPTIONS -v tc.polarity:20 -v tc.proj.like:10 -v tc.pos:10  --show-implicit #-}
-- {-# OPTIONS -v tc.pos.occ:70  #-}

open import Common.Prelude
open import Common.Product

dup : (b : Bool) (X : Set) → Set × Set
dup true  X = (X → X) , X
dup false X = (X → X) , X

postulate b : Bool

data D : Set where
  c : proj₁ (dup b D) → D

-- ERROR WAS:
-- D is not strictly positive, because it occurs
-- in the second argument to dup
-- in the type of the constructor c
-- in the definition of D.

-- EXPECTED ERROR:
-- D is not strictly positive, because it occurs
-- in the second argument to dup
-- in the first argument to proj₁
-- in the type of the constructor c
-- in the definition of D.
