module Issue1486 where

open import Common.Prelude

postulate
  QName : Set
{-# BUILTIN QNAME QName #-}

primitive
  primShowQName : QName -> String

main : IO Unit
main = putStrLn (primShowQName (quote main))
