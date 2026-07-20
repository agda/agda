{-# OPTIONS -v treeless.opt.simpl:30 -v 0 #-}

module Issue7595 where

open import Agda.Builtin.Maybe using (Maybe; just; nothing)

data Cell : Set where
  [-] [o] [x] : Cell

data Board : Set where
  mk-Board :
    (_ _ _
     _ _ _
     _ _ _ : Cell) → Board

winner : Board → Maybe Cell
winner = λ where
  (mk-Board [x]  _   _
            [x]  _   _
            [x]  _   _) → just [x]

  (mk-Board  _  [x]  _
             _  [x]  _
             _  [x]  _) → just [x]

  (mk-Board  _   _  [x]
             _   _  [x]
             _   _  [x]) → just [x]

  (mk-Board [x] [x] [x]
             _   _   _
             _   _   _ ) → just [x]

  (mk-Board  _   _   _
            [x] [x] [x]
             _   _   _ ) → just [x]

  (mk-Board  _   _   _
             _   _   _
            [x] [x] [x]) → just [x]

  (mk-Board [x]  _   _
             _  [x]  _
             _   _  [x]) → just [x]

  (mk-Board  _   _  [x]
             _  [x]  _
            [x]  _   _ ) → just [x]

  (mk-Board [o]  _   _
            [o]  _   _
            [o]  _   _ ) → just [o]

  (mk-Board  _  [o]  _
             _  [o]  _
             _  [o]  _ ) → just [o]

  (mk-Board  _   _  [o]
             _   _  [o]
             _   _  [o]) → just [o]

  (mk-Board [o] [o] [o]
             _   _   _
             _   _   _ ) → just [o]

  (mk-Board  _   _   _
            [o] [o] [o]
             _   _   _ ) → just [o]

  (mk-Board  _   _   _
             _   _   _
            [o] [o] [o]) → just [o]

  (mk-Board [o]  _   _
              _  [o]  _
              _   _  [o]) → just [o]

  (mk-Board  _   _  [o]
             _  [o]  _
            [o]  _   _ ) → just [o]

  (mk-Board [-]  _   _
             _   _   _
             _   _   _ ) → nothing

  (mk-Board  _  [-]  _
             _   _   _
             _   _   _ ) → nothing

  (mk-Board  _   _  [-]
             _   _   _
             _   _   _ ) → nothing

  (mk-Board  _   _   _
            [-]  _   _
             _   _   _ ) → nothing

  (mk-Board  _   _   _
             _  [-]  _
             _   _   _ ) → nothing

  (mk-Board  _   _   _
             _   _  [-]
             _   _   _ ) → nothing

  (mk-Board  _   _   _
             _   _   _
            [-]  _   _ ) → nothing

  (mk-Board  _   _   _
             _   _   _
             _  [-]  _ ) → nothing

  (mk-Board  _   _   _
             _   _   _
             _   _  [-]) → nothing

  (mk-Board  _   _   _
             _   _   _
             _   _   _ ) → just [-]

b0 : Board
b0 = mk-Board
  [-] [-] [-]
  [-] [-] [-]
  [-] [-] [-]

step : Board → Board
step b with winner b
... | just _ = b
... | nothing = b0

