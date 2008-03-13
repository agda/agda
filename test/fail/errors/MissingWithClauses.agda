module MissingWithClauses where

data D : Set where
  c : D

f : D -> D
f c with c
