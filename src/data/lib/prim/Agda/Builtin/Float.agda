{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness #-}

module Agda.Builtin.Float where

open import Agda.Builtin.Bool
open import Agda.Builtin.Int
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Word

postulate Float : Set
{-# BUILTIN FLOAT Float #-}

primitive
  -- Relations
  primFloatInequality        : Float → Float → Bool
  primFloatEquality          : Float → Float → Bool
  primFloatLess              : Float → Float → Bool
  primFloatIsInfinite        : Float → Bool
  primFloatIsNaN             : Float → Bool
  primFloatIsNegativeZero    : Float → Bool
  primFloatIsSafeInteger     : Float → Bool
  -- Conversions
  primFloatToWord64          : Float → Word64
  primNatToFloat             : Nat → Float
  primIntToFloat             : Int → Float
  primFloatRound             : Float → Maybe Int
  primFloatFloor             : Float → Maybe Int
  primFloatCeiling           : Float → Maybe Int
  primFloatToRatio           : Float → (Σ Int λ _ → Int)
  primRatioToFloat           : Int → Int → Float
  primFloatDecode            : Float → Maybe (Σ Int λ _ → Int)
  primFloatEncode            : Int → Int → Maybe Float
  primShowFloat              : Float → String
  -- Operations
  primFloatPlus              : Float → Float → Float
  primFloatMinus             : Float → Float → Float
  primFloatTimes             : Float → Float → Float
  primFloatDiv               : Float → Float → Float
  primFloatPow               : Float → Float → Float
  primFloatNegate            : Float → Float
  primFloatSqrt              : Float → Float
  primFloatExp               : Float → Float
  primFloatLog               : Float → Float
  primFloatSin               : Float → Float
  primFloatCos               : Float → Float
  primFloatTan               : Float → Float
  primFloatASin              : Float → Float
  primFloatACos              : Float → Float
  primFloatATan              : Float → Float
  primFloatATan2             : Float → Float → Float
  primFloatSinh              : Float → Float
  primFloatCosh              : Float → Float
  primFloatTanh              : Float → Float
  primFloatASinh             : Float → Float
  primFloatACosh             : Float → Float
  primFloatATanh             : Float → Float

{-# COMPILE JS
    primFloatRound = function(x) {
        x = agdaRTS._primFloatRound(x);
        if (x === null) {
            return z_jAgda_Agda_Builtin_Maybe["Maybe"]["nothing"];
        }
        else {
            return z_jAgda_Agda_Builtin_Maybe["Maybe"]["just"](x);
        }
    };
#-}
{-# COMPILE JS
    primFloatFloor = function(x) {
        x = agdaRTS._primFloatFloor(x);
        if (x === null) {
            return z_jAgda_Agda_Builtin_Maybe["Maybe"]["nothing"];
        }
        else {
            return z_jAgda_Agda_Builtin_Maybe["Maybe"]["just"](x);
        }
    };
#-}
{-# COMPILE JS
    primFloatCeiling = function(x) {
        x = agdaRTS._primFloatCeiling(x);
        if (x === null) {
            return z_jAgda_Agda_Builtin_Maybe["Maybe"]["nothing"];
        }
        else {
            return z_jAgda_Agda_Builtin_Maybe["Maybe"]["just"](x);
        }
    };
#-}
{-# COMPILE JS
    primFloatToRatio = function(x) {
        x = agdaRTS._primFloatToRatio(x);
        return z_jAgda_Agda_Builtin_Sigma["_,_"](x.numerator)(x.denominator);
    };
#-}
{-# COMPILE JS
    primFloatDecode = function(x) {
        x = agdaRTS._primFloatDecode(x);
        if (x === null) {
            return z_jAgda_Agda_Builtin_Maybe["Maybe"]["nothing"];
        }
        else {
            return z_jAgda_Agda_Builtin_Maybe["Maybe"]["just"](
                z_jAgda_Agda_Builtin_Sigma["_,_"](x.mantissa)(x.exponent));
        }
    };
#-}
{-# COMPILE JS
    primFloatEncode = function(x) {
        return function (y) {
            x = agdaRTS.uprimFloatEncode(x, y);
            if (x === null) {
                return z_jAgda_Agda_Builtin_Maybe["Maybe"]["nothing"];
            }
            else {
                return z_jAgda_Agda_Builtin_Maybe["Maybe"]["just"](x);
            }
        }
    };
#-}

primFloatNumericalEquality = primFloatEquality
{-# WARNING_ON_USAGE primFloatNumericalEquality
"Warning: primFloatNumericalEquality was deprecated in Agda v2.6.2.
Please use primFloatEquality instead."
#-}

primFloatNumericalLess = primFloatLess
{-# WARNING_ON_USAGE primFloatNumericalLess
"Warning: primFloatNumericalLess was deprecated in Agda v2.6.2.
Please use primFloatLess instead."
#-}

primRound = primFloatRound
{-# WARNING_ON_USAGE primRound
"Warning: primRound was deprecated in Agda v2.6.2.
Please use primFloatRound instead."
#-}

primFloor = primFloatFloor
{-# WARNING_ON_USAGE primFloor
"Warning: primFloor was deprecated in Agda v2.6.2.
Please use primFloatFloor instead."
#-}

primCeiling = primFloatCeiling
{-# WARNING_ON_USAGE primCeiling
"Warning: primCeiling was deprecated in Agda v2.6.2.
Please use primFloatCeiling instead."
#-}

primExp = primFloatExp
{-# WARNING_ON_USAGE primExp
"Warning: primExp was deprecated in Agda v2.6.2.
Please use primFloatExp instead."
#-}

primLog = primFloatLog
{-# WARNING_ON_USAGE primLog
"Warning: primLog was deprecated in Agda v2.6.2.
Please use primFloatLog instead."
#-}

primSin = primFloatSin
{-# WARNING_ON_USAGE primSin
"Warning: primSin was deprecated in Agda v2.6.2.
Please use primFloatSin instead."
#-}

primCos = primFloatCos
{-# WARNING_ON_USAGE primCos
"Warning: primCos was deprecated in Agda v2.6.2.
Please use primFloatCos instead."
#-}

primTan = primFloatTan
{-# WARNING_ON_USAGE primTan
"Warning: primTan was deprecated in Agda v2.6.2.
Please use primFloatTan instead."
#-}

primASin = primFloatASin
{-# WARNING_ON_USAGE primASin
"Warning: primASin was deprecated in Agda v2.6.2.
Please use primFloatASin instead."
#-}


primACos = primFloatACos
{-# WARNING_ON_USAGE primACos
"Warning: primACos was deprecated in Agda v2.6.2.
Please use primFloatACos instead."
#-}

primATan = primFloatATan
{-# WARNING_ON_USAGE primATan
"Warning: primATan was deprecated in Agda v2.6.2.
Please use primFloatATan instead."
#-}

primATan2 = primFloatATan2
{-# WARNING_ON_USAGE primATan2
"Warning: primATan2 was deprecated in Agda v2.6.2.
Please use primFloatATan2 instead."
#-}
