
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
  putStr "123.4 = " ,, print 123.4 ,,
  putStr "-42.9 = " ,, print -42.9 ,,
  putStr "NaN   = " ,, print NaN   ,,
  putStr "Inf   = " ,, print Inf   ,,
  putStr "-Inf  = " ,, print -Inf  ,,
  putStr "Inf == Inf  = " ,, printB (Inf == Inf) ,,
  putStr "NaN < -Inf  = " ,, printB (NaN < -Inf) ,,
  -- Issues #2155 and #2194.
  putStr "NaN == NaN  = " ,, printB (NaN == NaN) ,,
  -- Issue #2169.
  putStr "0.0 == -0.0 = " ,, printB (0.0 == -0.0) ,,
  return unit
