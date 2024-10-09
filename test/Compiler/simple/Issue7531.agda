-- Test case by Lawrence Chonavel

open import Agda.Builtin.Bool
open import Common.IO
open import Common.Unit

data Cell : Set where
  [-] [o] [x] : Cell

data Board : Set where
  mk-Board : (
    _ _ _
    _ _ _
    _ _ _ : Cell)
    → Board

game-over : Board → Bool
game-over = λ where
  (mk-Board [x]  _   _
            [x]  _   _
            [x]  _   _  ) → true

  (mk-Board  _  [x]  _
             _  [x]  _
             _  [x]  _  ) → true

  (mk-Board  _   _  [x]
             _   _  [x]
             _   _  [x] ) → true

  (mk-Board [x] [x] [x]
             _   _   _
             _   _   _  ) → true

  (mk-Board  _   _   _
            [x] [x] [x]
             _   _   _  ) → true

  (mk-Board  _   _   _
             _   _   _
            [x] [x] [x] ) → true

  (mk-Board [x]  _   _
             _  [x]  _
             _   _  [x] ) → true

  (mk-Board  _   _   _
             _   _   _
             _   _   _  ) → false

main : IO Unit
main = printBool (game-over
  (mk-Board [x] [-] [-]
            [-] [x] [-]
            [-] [-] [x] ))
