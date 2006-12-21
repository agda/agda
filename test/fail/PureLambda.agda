
module PureLambda where

data D : Set where
  lam : (D -> D) -> D

_·_ : D -> D -> D
lam f · x = f x

δ : D
δ = lam (\x -> x · x)

loop : D
loop = δ · δ

