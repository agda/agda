
module Imports.Unsolved where

X : Set
X = ?

-- Fails with proof-irrelevance (to make this fail by itself)
data Two : Prop where
  one : Two
  two : Two

