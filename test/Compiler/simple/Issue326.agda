
module Issue326 where

open import Common.Prelude

postulate
  QName : Set

{-# BUILTIN QNAME QName #-}

primitive primQNameEquality : QName → QName → Bool

main : IO Unit
main = printBool (primQNameEquality (quote Unit) (quote IO))
