{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness #-}

module Agda.Builtin.Float where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Int
open import Agda.Builtin.String

{-# BUILTIN FLOAT Float #-}

primitive
  primFloatEquality : Float → Float → Bool
  primFloatLess     : Float → Float → Bool
  primFloatNumericalEquality : Float → Float → Bool
  primFloatNumericalLess     : Float → Float → Bool
  primNatToFloat    : Nat → Float
  primFloatPlus     : Float → Float → Float
  primFloatMinus    : Float → Float → Float
  primFloatTimes    : Float → Float → Float
  primFloatNegate   : Float → Float
  primFloatDiv      : Float → Float → Float
  primFloatSqrt     : Float → Float
  primRound         : Float → Int
  primFloor         : Float → Int
  primCeiling       : Float → Int
  primExp           : Float → Float
  primLog           : Float → Float
  primSin           : Float → Float
  primCos           : Float → Float
  primTan           : Float → Float
  primASin          : Float → Float
  primACos          : Float → Float
  primATan          : Float → Float
  primATan2         : Float → Float → Float
  primShowFloat     : Float → String
