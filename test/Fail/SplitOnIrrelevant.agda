-- 2010-09-07 Andreas
-- 2011-10-04 may not work even in the presence of experimental irr.
{-# OPTIONS --experimental-irrelevance #-}
module SplitOnIrrelevant where

data Bool : Set where
  true false : Bool

not : .Bool -> Bool
not true = false  -- needs to fail
not false = true
