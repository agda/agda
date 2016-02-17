
module _ where

open import Agda.Builtin.Float
open import Common.Prelude hiding (_+_; _*_)

print : Float → IO Unit
print x = putStrLn (primShowFloat x)

printB : Bool → IO Unit
printB true  = putStrLn "true"
printB false = putStrLn "false"

_+_ = primFloatPlus
_*_ = primFloatTimes
_/_ = primFloatDiv
_==_ = primFloatEquality
_<_ = primFloatLess

NaN : Float
NaN = 0.0 / 0.0

Inf : Float
Inf = 1.0 / 0.0

-Inf : Float
-Inf = -1.0 / 0.0

pi : Float
pi = 3.141592653589793


main : IO Unit
main =
  putStr "123.0 = " ,, print 123.0 ,,
  putStr "NaN   = " ,, print NaN   ,,
  putStr "Inf   = " ,, print Inf   ,,
  putStr "-Inf  = " ,, print -Inf  ,,
  putStr "-0.0  = " ,, print -0.0  ,,
  -- Disabled due to #1856 and #1857
  -- putStr "√2    = " ,, print (primFloatTimes 2.0 (primSin (primFloatDiv pi 4.0))) ,,
  -- putStr "e     = " ,, print (primExp 1.0) ,,
  putStr "NaN == NaN = " ,, printB (NaN == NaN) ,,
  putStr "Inf == Inf = " ,, printB (Inf == Inf) ,,
  putStr "NaN < -Inf = " ,, printB (NaN < -Inf) ,,
  putStr "NaN < -5.0 = " ,, printB (NaN < -5.0) ,,
  return unit
