
module Issue326 where

open import Common.Prelude
open import Common.MAlonzo using () -- see issue 561

postulate
  QName : Set
  printBool : Bool → IO Unit

{-# BUILTIN QNAME QName #-}
{-# COMPILED printBool print #-}

primitive primQNameEquality : QName → QName → Bool

main : IO Unit
main = printBool (primQNameEquality (quote Unit) (quote IO))
