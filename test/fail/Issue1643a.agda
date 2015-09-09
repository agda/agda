-- Andreas, 2015-09-09 Issue 1643
-- {-# OPTIONS -v tc.mod.apply:20 #-}
-- {-# OPTIONS -v tc.signature:30 #-}
-- {-# OPTIONS -v tc.display:100  #-}
-- {-# OPTIONS -v scope:50 -v scope.inverse:100 -v interactive.meta:20 #-}

module _ where

module M where
  postulate A : Set

module N = M  -- This alias used to introduce a display form M.A --> N.A

open N

postulate
  a : A

test : Set
test = a

-- ERROR SHOULD BE:   A !=< Set of type Set
