
module Issue478b where

record Ko (Q : Set) : Set₁ where
  field
    T : Set

  foo : T
  foo = Set

-- This previously said Set₁ !=< T r