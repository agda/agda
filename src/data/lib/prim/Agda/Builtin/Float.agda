{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness
            --no-subtyping #-}

module Agda.Builtin.Float where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Int
open import Agda.Builtin.Word
open import Agda.Builtin.Sigma
open import Agda.Builtin.String

postulate Float : Set
{-# BUILTIN FLOAT Float #-}

primitive
  primFloatToWord64 : Float → Word64
  primFloatToRatio  : Float → Σ Int (λ _ → Nat)
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

{-# COMPILE JS primFloatToRatio = function(x) {
    if (x !== x) {
      return z_jAgda_Agda_Builtin_Sigma["_,_"](0)(0);
    }
    else if (x === Infinity) {
      return z_jAgda_Agda_Builtin_Sigma["_,_"](1)(0);
    }
    else if (x === -Infinity) {
      return z_jAgda_Agda_Builtin_Sigma["_,_"](-1)(0);
    }
    else {
      return z_jAgda_Agda_Builtin_Sigma["_,_"](Math.round(x*10e8))(10e8);
    }
  }
#-}

