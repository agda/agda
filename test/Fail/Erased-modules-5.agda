{-# OPTIONS --erasure #-}

module Erased-modules-5 where

module @0 M (@0 A : Set) where

  B : Set
  B = A

-- Everything in the module N is erased.

module @0 N (A : Set) = M A

_ : Set → Set
_ = N.B
