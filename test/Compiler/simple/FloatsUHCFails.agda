-- ASR (2016-09-16). These tests are disabled with the UHC
-- backend. After fixing a test to merge it into the `Floats` tests.

module _ where

open import Common.Prelude

print : Float → IO Unit
print x = putStrLn (primShowFloat x)

pi : Float
pi = 3.141592653589793

sin = primSin
cos = primCos
tan = primTan
asin = primASin
acos = primACos
atan = primATan
atan2 = primATan2


main : IO Unit
main =
  putStr "sin (asin 0.6) = " ,, print (sin (asin 0.6)) ,,
  putStr "cos (acos 0.6) = " ,, print (cos (acos 0.6)) ,,
  putStr "tan (atan 0.6) = " ,, print (tan (atan 0.6)) ,,
  putStr "tan (atan2 0.6 1.0) = " ,, print (tan (atan2 0.6 1.0)) ,,
  -- See Issues #1856 and #1857.
  putStr "√2 = " ,, print (primFloatSqrt 2.0) ,,
  putStr "√2 = " ,, print (primFloatTimes 2.0 (primSin (primFloatDiv pi 4.0))) ,,

  -- See Issue #1856.
  putStr "e = " ,, print (primExp 1.0) ,,
  return unit
