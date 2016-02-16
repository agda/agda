
module Agda.Builtin.Float where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Int
open import Agda.Builtin.String

postulate Float : Set
{-# BUILTIN FLOAT Float #-}

primitive
  primFloatEquality : Float → Float → Bool
  primFloatLess     : Float → Float → Bool
  primNatToFloat    : Nat → Float
  primFloatPlus     : Float → Float → Float
  primFloatMinus    : Float → Float → Float
  primFloatTimes    : Float → Float → Float
  primFloatDiv      : Float → Float → Float
  primFloatSqrt     : Float → Float
  primRound         : Float → Int
  primFloor         : Float → Int
  primCeiling       : Float → Int
  primExp           : Float → Float
  primLog           : Float → Float
  primSin           : Float → Float
  primShowFloat     : Float → String
