-- Andreas, 2012-10-02
-- {-# OPTIONS -v tc.conv.level:100 -v tc.constr.add:40 -v tc.meta:50 -v tc.inj.use:30 -v 80 #-}
module Issue689 where

open import Common.Level

data Bad : Set₁ where
  c : Set₁ → Bad

-- this should not leave unsolvable constraints, but report an error
