-- Cross-backend semantic coverage for the nested-case simplification in #7595.

open import Agda.Builtin.Maybe
open import Common.IO
open import Common.String
open import Common.Unit

case_of_ : {A B : Set} -> A -> (A -> B) -> B
case x of f = f x

data Cell : Set where
  [-] [x] : Cell

data Board : Set where
  mk-Board : Cell -> Cell -> Board

winner : Board -> Maybe Cell
winner = \ where
  (mk-Board [x] [x]) -> just [x]
  (mk-Board [-]  _ ) -> nothing
  (mk-Board  _  [-]) -> nothing

b0 : Board
b0 = mk-Board [-] [-]

bx : Board
bx = mk-Board [x] [x]

step1 : Board -> Board
step1 b = case winner b of \ where
  (just _) -> b
  nothing  -> b0

step2 : Board -> Board
step2 b with winner b
... | just _ = b
... | nothing = b0

showWinner : Maybe Cell -> String
showWinner nothing    = "nothing"
showWinner (just [-]) = "-"
showWinner (just [x]) = "x"

printWinner : Board -> IO Unit
printWinner b = putStr (showWinner (winner b)) >>= \ _ -> putStr "\n"

main : IO Unit
main =
  printWinner (step1 b0) >>= \ _ ->
  printWinner (step2 b0) >>= \ _ ->
  printWinner (step1 bx) >>= \ _ ->
  printWinner (step2 bx)
