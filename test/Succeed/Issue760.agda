module Issue760 where

module M where
  A : Set₂
  A = Set₁

abstract
  B : Set₁
  B = Set

  open M public  -- Not abstract.


  C : Set₁
  C = F where
    F = Set -- where clauses declare an anonymous open public module
            -- but we should not see any error here

InScope : A
InScope = Set

private
  D : Set₁
  D = Set

  open M public  -- Private & public?!

  E : Set₁
  E = F where
    F = Set -- where clauses declare an anonymous open public module
            -- but we should not see any error here
