{-# OPTIONS --erasure #-}

module Erased-modules-6 where

module @0 M (@0 A : Set) where

  B : Set
  B = A

-- Everything in the module N is erased.

open module @0 N (@0 A : Set) = M A

_ : @0 Set → Set
_ = N.B
