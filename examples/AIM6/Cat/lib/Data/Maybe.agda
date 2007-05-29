
module Data.Maybe where

data Maybe (a : Set) : Set where
  nothing : Maybe a
  just	  : a -> Maybe a


