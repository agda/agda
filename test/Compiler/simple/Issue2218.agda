
open import Agda.Builtin.Float
open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection
open import Agda.Builtin.String
open import Agda.Builtin.Bool
open import Common.IO

data It (a : Float) : Set where
  it : It a

inf : Float
inf = primFloatDiv 1.0 0.0

-inf : Float
-inf = primFloatNegate inf

nan : Float
nan = primFloatDiv 0.0 0.0

-nan : Float
-nan = primFloatNegate nan

_==_ = primFloatEquality

macro
  literal : Float → Term → TC ⊤
  literal x hole = unify hole (lit (float x))

nl = putStrLn ""

header = putStrLn " inf  -inf   nan  -nan  |  x"

tick : Bool → String
tick true  = "   x  "
tick false = "   -  "

check : Float → IO _
check x = putStr (tick (x ==  inf)) ,,
          putStr (tick (x == -inf)) ,,
          putStr (tick (x ==  nan)) ,,
          putStr (tick (x == -nan)) ,,
          putStr "|  " ,, printFloat x ,,
          nl

main : IO _
main =
  header ,,
  check (literal  inf) ,,
  check (literal -inf) ,,
  check (literal  nan) ,,
  check (literal -nan)
