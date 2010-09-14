module Issue309a where

data D : Set where
  d : D → D

syntax d x x = e x

g : D → D
g (d x) = e x
