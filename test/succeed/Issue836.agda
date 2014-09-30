-- Andreas, 2013-05-02 This ain't a bug, it is a feature.
-- {-# OPTIONS -v scope.name:10 #-}
-- {-# OPTIONS -v scope:10 #-}

module Issue836 where

module M where

  record R : Set₁ where
    field
      X : Set

open M using (R)

X : R → Set
X = R.X

-- A glimpse at the scope (showing only concrete names, though):
--   modules
--     * scope Issue836
--       private names   R --> [Issue836.M.R]
--       public  modules M --> [Issue836.M]
--     * scope Issue836.M
--       public  names   R --> [Issue836.M.R]
--               modules R --> [Issue836.M.R]
--     * scope Issue836.M.R
--       public  names   X --> [Issue836.M.R.X]

-- Nisse:
-- The open directive did not mention the /module/ R, so (I think
-- that) the code above should be rejected.

-- Andreas:
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

open import Common.Equality

twoWaysToQualify : D.c ≡ MD.c
twoWaysToQualify = refl

