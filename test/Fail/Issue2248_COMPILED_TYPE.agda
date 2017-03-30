-- Andreas, 2016-10-11, AIM XXIV, issue #2248
-- COMPILED_TYPE should only work on postulates
-- Andreas, 2017-03-39, issue #2524
-- Relax this to abstract atoms.
-- Currently we still forbid this on abstract functions.

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

{-# COMPILE GHC IO' = type IO #-}  -- is rejected

postulate
  toIO : {A : Set} → IO' A → IO A

{-# COMPILE GHC toIO = \ _ x -> x #-}

main : IO Unit
main = toIO doNothing
