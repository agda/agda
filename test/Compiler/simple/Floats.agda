
module _ where

open import Common.Prelude

open import Agda.Builtin.Float public
  using (Float)
  renaming
  -- Relations
  ( primFloatInequality        to infix 4 _≤ᵇ_
  ; primFloatEquality          to infix 4 _≡ᵇ_
  ; primFloatLess              to infix 4 _<ᵇ_
  ; primFloatIsInfinite        to isInfinite
  ; primFloatIsNaN             to isNaN
  ; primFloatIsDenormalized    to isDenormalized
  ; primFloatIsNegativeZero    to isNegativeZero
  ; primFloatIsSafeInteger     to isSafeInteger
  -- Conversions
  ; primFloatToWord64          to toWord
  ; primNatToFloat             to fromℕ
  ; primIntToFloat             to fromℤ
  ; primFloatRound             to round
  ; primFloatFloor             to ⌊_⌋
  ; primFloatCeiling           to ⌈_⌉
  ; primFloatToRatio           to toRatio
  ; primRatioToFloat           to fromRatio
  ; primFloatDecode            to decode
  ; primFloatEncode            to encode
  ; primShowFloat              to show
  -- Operations
  ; primFloatPlus              to infixl 6 _+_
  ; primFloatMinus             to infixl 6 _-_
  ; primFloatTimes             to infixl 7 _*_
  ; primFloatDiv               to infixl 7 _÷_
  ; primFloatPow               to infix  8 _**_
  ; primFloatNegate            to infix  9 -_
  ; primFloatSqrt              to sqrt
  ; primFloatExp               to e^_
  ; primFloatLog               to log
  ; primFloatSin               to sin
  ; primFloatCos               to cos
  ; primFloatTan               to tan
  ; primFloatASin              to asin
  ; primFloatACos              to acos
  ; primFloatATan              to atan
  ; primFloatATan2             to atan2
  ; primFloatSinh              to sinh
  ; primFloatCosh              to cosh
  ; primFloatTanh              to tanh
  ; primFloatASinh             to asinh
  ; primFloatACosh             to acosh
  ; primFloatATanh             to atanh
  )

printF : Float → IO Unit
printF x = putStrLn (primShowFloat x)

printB : Bool → IO Unit
printB true  = putStrLn "true"
printB false = putStrLn "false"

NaN -NaN Infinity -Infinity : Float
NaN = 0.0 ÷ 0.0
-NaN = - NaN
Infinity = 1.0 ÷ 0.0
-Infinity = - Infinity

isZero : Float → String
isZero x =
  if isNegativeZero x
  then "neg"
  else if x ≡ᵇ 0.0
       then "pos"
       else "nonzero"

main : IO Unit
main =
  putStr "123.4 = " ,, printF 123.4 ,,
  putStr "-42.9 = " ,, printF -42.9 ,,
  putStr "1.0 = " ,, printF 1.0   ,,
  putStr "-0.0 = " ,, printF -0.0  ,,

  putStr "NaN = " ,, printF NaN ,,
  putStr "Infinity = " ,, printF Infinity ,,
  putStr "-Infinity = " ,, printF -Infinity ,,

  -- Issues #2155 and #2194.
  putStr "Infinity ≡ᵇ Infinity = " ,, printB (Infinity ≡ᵇ Infinity) ,,
  putStr "NaN ≡ᵇ  NaN = " ,, printB (NaN ≡ᵇ NaN) ,,
  -- Issue #2194.
  putStr "NaN ≡ᵇ -NaN = " ,, printB (NaN ≡ᵇ (primFloatNegate NaN)) ,,
  -- Issue #2169.
  putStr "0.0 ≡ᵇ -0.0 = " ,, printB (0.0 ≡ᵇ -0.0) ,,

  -- Issue #2216
  putStr "isZero 0.0 = " ,, putStrLn (isZero 0.0) ,,
  putStr "isZero -0.0 = " ,, putStrLn (isZero -0.0) ,,
  putStr "isZero 1.0 = " ,, putStrLn (isZero 1.0) ,,

  -- Numerical equality
  putStr "NaN ≡ᵇ NaN  = " ,, printB (NaN ≡ᵇ NaN) ,,
  putStr "0.0 ≡ᵇ -0.0 = " ,, printB (0.0 ≡ᵇ -0.0) ,,
  putStr "0.0 ≡ᵇ 12.0 = " ,, printB (0.0 ≡ᵇ 12.0) ,,
  putStr "NaN  <ᵇ -Infinity = " ,, printB (NaN <ᵇ -Infinity) ,,
  putStr "-Infinity <ᵇ NaN  = " ,, printB (-Infinity <ᵇ NaN) ,,
  putStr "0.0  <ᵇ -0.0 = " ,, printB (0.0 <ᵇ -0.0) ,,
  putStr "-0.0 <ᵇ 0.0  = " ,, printB (-0.0 <ᵇ 0.0) ,,

  -- Issue #2208.
  putStr "NaN  <ᵇ NaN  = " ,, printB (NaN <ᵇ NaN) ,,
  putStr "-NaN <ᵇ -NaN = " ,, printB (-NaN <ᵇ -NaN) ,,
  putStr "NaN  <ᵇ -NaN = " ,, printB (NaN <ᵇ -NaN) ,,
  putStr "-NaN <ᵇ NaN  = " ,, printB (-NaN <ᵇ NaN) ,,
  putStr "NaN  <ᵇ -5.0 = " ,, printB (NaN <ᵇ -5.0) ,,
  putStr "-5.0 <ᵇ NaN  = " ,, printB (-5.0 <ᵇ NaN) ,,

  putStr "NaN  <ᵇ -Infinity = " ,, printB (NaN <ᵇ -Infinity) ,,
  putStr "-Infinity <ᵇ NaN  = " ,, printB (-Infinity <ᵇ NaN) ,,
  putStr "0.0  <ᵇ -0.0 = " ,, printB (0.0 <ᵇ -0.0) ,,
  putStr "-0.0 <ᵇ 0.0  = " ,, printB (-0.0 <ᵇ 0.0) ,,

  -- Issue #2208.
  putStr "NaN  <ᵇ NaN  = " ,, printB (NaN <ᵇ NaN) ,,
  putStr "-NaN <ᵇ -NaN = " ,, printB (-NaN <ᵇ -NaN) ,,
  putStr "NaN  <ᵇ -NaN = " ,, printB (NaN <ᵇ -NaN) ,,
  putStr "-NaN <ᵇ NaN  = " ,, printB (-NaN <ᵇ NaN) ,,
  putStr "NaN  <ᵇ -5.0 = " ,, printB (NaN <ᵇ -5.0) ,,
  putStr "-5.0 <ᵇ NaN  = " ,, printB (-5.0 <ᵇ NaN) ,,

  putStr "e                   = " ,, printF (e^ 1.0) ,,
  putStr "sin (asin 0.6)      = " ,, printF (sin (asin 0.6)) ,,
  putStr "cos (acos 0.6)      = " ,, printF (cos (acos 0.6)) ,,
  putStr "tan (atan 0.4)      = " ,, printF (tan (atan 0.4)) ,,
  putStr "tan (atan2 0.4 1.0) = " ,, printF (tan (atan2 0.4 1.0)) ,,

  return unit
