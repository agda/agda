module Issue296 where

postulate
  Unit : Set
  IO   : Set → Set
  foo  : ((A B : Set) → Unit) → IO Unit
  bar  : (A B : Set) → Unit

{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}
{-# COMPILE GHC Unit = type () #-}
{-# COMPILE GHC bar = undefined #-}

main : IO Unit
main = foo bar
