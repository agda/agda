{-# OPTIONS --no-termination-check #-}

module Data.Bits where

import Prelude
import Logic.Base
import Data.List as List
import Data.Nat  as Nat
import Data.Bool as Bool

open Prelude
open Nat
open Bool
open List

Bit = Bool

shiftL : Nat -> Nat -> Nat
shiftL n i = n * 2 ^ i

sucBits : List Bit -> List Bit
sucBits []            = true :: []
sucBits (false :: xs) = true :: xs
sucBits (true  :: xs) = false :: sucBits xs

-- Least significant bit first. Last bit (when present) is always one.
toBits : Nat -> List Bit
toBits zero    = []
toBits (suc n) = sucBits (odd n :: toBits (div n 2))

fromBits : List Bit -> Nat
fromBits xs = foldr (\b n -> bitValue b + 2 * n) 0 xs
  where
    bitValue : Bit -> Nat
    bitValue b = if b then 1 else 0

nofBits : Nat -> Nat
nofBits = length ∘ toBits

module Proofs where

  open Logic.Base

--   fromBits∘toBits=id : (n : Nat) -> fromBits (toBits n) ≡ n
--   fromBits∘toBits=id  zero   = tt
--   fromBits∘toBits=id (suc n) = ?

