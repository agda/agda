-- Andreas, 2012-11-22 abstract aliases
module Issue729 where

abstract
  B = Set
  B₁ = B
  B₂ = Set

abstract
  foo : Set₁
  foo = x
    where x = B

{- does not work yet
mutual
 abstract
  D = C
  C = B
-}

-- other stuff

private
  A = Set

Y = let X = Set in Set
