-- Andreas, 2011-04-15
-- {-# OPTIONS -v tc.data:20 #-}
module IrrelevantDataParameter where

postulate 
  A : Set

data K .(a : A) : Set where
  c : K a

postulate
  a : A

data K' .(b : A) : Set where
  c : K' a
-- ok, since parameter irrelevant

