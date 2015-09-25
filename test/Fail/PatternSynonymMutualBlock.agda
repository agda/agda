module PatternSynonymMutualBlock where

data D : Set where
  c : D

mutual
  pattern p = c
