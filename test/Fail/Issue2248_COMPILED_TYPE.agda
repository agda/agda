-- Andreas, 2016-10-11, AIM XXIV, issue #2248
-- COMPILED_TYPE should only work on postulates

data Unit : Set where
  unit : Unit

postulate
  IO : Set → Set

{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

abstract
  IO' : Set → Set
  IO' A = A

  doNothing : IO' Unit
  doNothing = unit

{-# COMPILE GHC IO' = type IO #-}

postulate
  toIO : {A : Set} → IO' A → IO A

{-# COMPILE GHC toIO = \ _ x -> x #-}

main : IO Unit
main = toIO doNothing
