{-# OPTIONS --guarded --cubical=compatible #-}
module Agda.Primitive.Guarded where

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : LockU
