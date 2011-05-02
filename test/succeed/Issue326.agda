
module Issue326 where

open import Common.Prelude

postulate
  QName : Set
  Unit : Set
  IO   : Set → Set
  printBool : Bool → IO Unit

{-# BUILTIN QNAME QName #-}
{-# BUILTIN IO IO #-}
{-# COMPILED_TYPE IO IO #-}
{-# COMPILED_TYPE Unit () #-}
{-# COMPILED printBool print #-}

primitive primQNameEquality : QName → QName → Bool

main : IO Unit
main = printBool (primQNameEquality (quote Unit) (quote IO))
