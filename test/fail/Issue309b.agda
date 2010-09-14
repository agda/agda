module Issue309b where

data D : Set where
  d : D → D

syntax d x = f

g : D → D
g (d x) = f
