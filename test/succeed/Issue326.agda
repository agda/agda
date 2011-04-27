
module Issue326 where

open import Common.Prelude
open import Common.Reflect

postulate
  Unit : Set
  IO   : Set → Set
  printBool : Bool → IO Unit

{-# BUILTIN IO IO #-}
{-# COMPILED_TYPE IO IO #-}
{-# COMPILED_TYPE Unit () #-}
{-# COMPILED printBool print #-}

main : IO Unit
main = printBool (primQNameEquality (quote Unit) (quote IO))
