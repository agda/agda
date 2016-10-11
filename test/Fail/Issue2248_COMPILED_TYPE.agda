-- Andreas, 2016-10-11, AIM XXIV, issue #2248
-- COMPILED_TYPE should only work on postulates

data Unit : Set where
  unit : Unit

abstract
  IO : Set → Set
  IO A = A

  doNothing : IO Unit
  doNothing = unit

{-# COMPILED_TYPE IO IO #-}

main : IO unit
main = doNothing
