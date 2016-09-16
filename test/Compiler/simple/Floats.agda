
module _ where

open import Common.Prelude

print : Float → IO Unit
print x = putStrLn (primShowFloat x)

printB : Bool → IO Unit
printB true  = putStrLn "true"
printB false = putStrLn "false"

_/_ = primFloatDiv
_==_ = primFloatEquality
_<_ = primFloatLess

NaN : Float
NaN = 0.0 / 0.0

Inf : Float
Inf = 1.0 / 0.0

-Inf : Float
-Inf = -1.0 / 0.0

main : IO Unit
main =
  putStr "NaN   = " ,, print NaN   ,,
  putStr "Inf   = " ,, print Inf   ,,
  putStr "-Inf  = " ,, print -Inf  ,,
  -- Disabled due to #1856 and #1857
  -- putStr "√2    = " ,, print (primFloatTimes 2.0 (primSin (primFloatDiv pi 4.0))) ,,
  -- putStr "e     = " ,, print (primExp 1.0) ,,
  putStr "Inf == Inf  = " ,, printB (Inf == Inf) ,,
  putStr "NaN < -Inf  = " ,, printB (NaN < -Inf) ,,
  return unit
