module Issue308b where

data D : Set where
  d : D → D

syntax d x = e x x

g : D → D
g (d x) = e x
