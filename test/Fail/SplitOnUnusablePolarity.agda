{-# OPTIONS --polarity #-}
module SplitOnUnusablePolarity where

data Bool : Set where
  true false : Bool

not : @unused Bool -> Bool
not true  = false
not false = true
