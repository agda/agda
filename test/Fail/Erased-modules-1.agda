{-# OPTIONS --erasure #-}

module Erased-modules-1 where

-- Everything in this local module is erased.

module @0 M (@0 A : Set) where

  B : Set
  B = A

_ : @0 Set → Set
_ = M.B
