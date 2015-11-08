module Issue296 where

postulate
  Unit : Set
  IO   : Set → Set
  foo  : ((A B : Set) → Unit) → IO Unit
  bar  : (A B : Set) → Unit

{-# BUILTIN IO IO #-}
{-# COMPILED_TYPE IO IO #-}
{-# COMPILED_TYPE Unit () #-}
{-# COMPILED bar undefined #-}

main : IO Unit
main = foo bar
