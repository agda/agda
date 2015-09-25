module Issue308a where

data D : Set where
  d : D → D

syntax d x = d d x

f : D → D
f x = d d x
