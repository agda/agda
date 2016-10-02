
open import Agda.Builtin.Float
open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection
open import Agda.Builtin.String
open import Agda.Builtin.Bool
open import Common.IO

data It (a : Float) : Set where
  it : It a

Inf : Float
Inf = primFloatDiv 1.0 0.0

-Inf : Float
-Inf = primFloatNegate Inf

NaN : Float
NaN = primFloatDiv 0.0 0.0

-NaN : Float
-NaN = primFloatNegate NaN

_==_ = primFloatEquality

macro
  literal : Float → Term → TC ⊤
  literal x hole = unify hole (lit (float x))

nl = putStrLn ""

header = putStrLn " Inf  -Inf   NaN  -NaN  |  x"

tick : Bool → String
tick true  = "   x  "
tick false = "   -  "

check : Float → IO _
check x = putStr (tick (x ==  Inf)) ,,
          putStr (tick (x == -Inf)) ,,
          putStr (tick (x ==  NaN)) ,,
          putStr (tick (x == -NaN)) ,,
          putStr "|  " ,, printFloat x ,,
          nl

main : IO _
main =
  header ,,
  check (literal  Inf) ,,
  check (literal -Inf) ,,
  check (literal  NaN) ,,
  check (literal -NaN)
