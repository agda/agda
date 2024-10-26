-- Test case by Lawrence Chonavel

open import Agda.Builtin.Bool
open import Common.IO
open import Common.Unit

data Cell : Set where
  [-] [o] [x] : Cell

data Board : Set where
  mk-Board : Cell → Cell → Board

winner : Board → Cell
winner = λ where
  (mk-Board [x] [x]) → [x]
  (mk-Board  _  [x]) → [x]
  (mk-Board  _   _ ) → [-]
{-# INLINE winner #-}

step : Board → Board
step b with winner b
... | [-] = b
... |  _  = mk-Board [-] [-]

isEmpty : Board → Bool
isEmpty (mk-Board [-] [-]) = true
isEmpty (mk-Board  _   _ ) = false

main : IO Unit
main = printBool (isEmpty (step (mk-Board [x] [x])))
