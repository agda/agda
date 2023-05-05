{-# OPTIONS --erasure #-}

module Erased-modules-2 where

-- Everything in the following anonymous module is erased.

module @0 _ where

  F : @0 Set → Set
  F A = A

_ : @0 Set → Set
_ = F
