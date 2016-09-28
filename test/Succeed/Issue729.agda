-- Andreas, 2012-11-22 issue #729, abstract aliases
-- Andreas, 2016-07-19 issue #2102, better fix of #418 helps!

module Issue729 where

abstract
  B = Set
  B₁ = B
  B₂ = Set

abstract
  foo : Set₁
  foo = x
    where x = B

mutual
  abstract
    D = C
    C = B

abstract
  mutual
    F = E
    E = D

-- other stuff

private
  A = Set

Y = let X = Set in Set
