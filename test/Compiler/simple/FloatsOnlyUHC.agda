-- ASR (2016-09-26). UHC and GHC have different behaviours. This test
-- only is enabled for the UHC backend.

-- Issue #1856: UHC prints doubles with lower precision than GHC
--
-- For example, printing √2
--
-- GHC (8.0.1):  1.4142135623730951
-- UHC (1.1.94): 1.414214

module _ where

open import Common.Prelude

print : Float → IO Unit
print x = putStrLn (primShowFloat x)

pi : Float
pi = 3.141593

main : IO Unit
main =
  -- Issue #1856.
  putStr "sqrt 2 = " ,, print (primFloatSqrt 2.0) ,,
  putStr "srqt 2 = " ,, print (primFloatTimes 2.0 (primSin (primFloatDiv pi 4.0))) ,,
  putStr "e =      " ,, print (primExp 1.0) ,,

  return unit
