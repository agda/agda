
module _ where

open import Common.Prelude

printB : Bool → IO Unit
printB true  = putStrLn "true"
printB false = putStrLn "false"

_==_ = primFloatEquality

main : IO Unit
main =
  putStr "0.0 == -0.0 = " ,, printB (0.0 == -0.0) ,,
  return unit
