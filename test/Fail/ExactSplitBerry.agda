{-# OPTIONS --exact-split -Werror #-}
module ExactSplitBerry where

data Bool : Set where
  true false : Bool

maj : Bool → Bool → Bool → Bool
maj true  true  true  = true
maj x     true  false = x
maj false y     true  = y
maj true  false z     = z
maj false false false = false
