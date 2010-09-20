
module Issue313 where

postulate
  QName : Set

{-# BUILTIN QNAME QName #-}

postulate
  X   : Set
  _+_ : QName → QName → Set

foo : Set
foo = quote X + quote X
