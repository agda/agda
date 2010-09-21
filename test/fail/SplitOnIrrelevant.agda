-- 2010-09-07 Andreas

module SplitOnIrrelevant where

data Bool : Set where
  true false : Bool

not : .Bool -> Bool
not true = false  -- needs to fail
not false = true
