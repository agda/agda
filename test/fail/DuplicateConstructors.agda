
module DuplicateConstructors where

data D : Set where
  c : D
  c : D

f : D -> D
f c = c
