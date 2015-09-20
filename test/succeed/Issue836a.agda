-- Andreas, 2013-05-02 This ain't a bug, it is a feature.
-- {-# OPTIONS -v scope.name:10 #-}
-- {-# OPTIONS -v scope:10 #-}
-- {-# OPTIONS -v scope.mod.inst:30 #-}
module _ where

module M (_ : Set₁) where

  record R : Set₁ where
    field
      X : Set

open M Set using (R)

X : R → Set
X = R.X

-- A glimpse at the scope (showing only concrete names, though)
--  modules
--   * scope Issue836a
--     private names   R --> [Issue836a._.R]
--     public  modules M --> [Issue836a.M]
--   * scope Issue836a.M
--     public  names   R --> [Issue836a.M.R]
--     public  modules R --> [Issue836a.M.R]
--   * scope Issue836a.M.R
--     public  names   X --> [Issue836a.M.R.X]
--   * scope Issue836a._
--     public  names   R --> [Issue836a._.R]
--     public  modules R --> [Issue836a._.R]
--   * scope Issue836a._.R
--     public  names   X --> [Issue836a._.R.X]

-- Nisse:
-- The open directive did not mention the /module/ R, so (I think
-- that) the code above should be rejected.

-- Andreas
-- NO, it is a feature that projections can also be accessed via
-- the record /type/.

-- The following directive is (and should be) rejected:

-- open R

-- Bug.agda:19,6-7
-- No such module R
-- when scope checking the declaration
--   open R
