
module NotStrictlyPositiveInMutual where

mutual
  data Cheat : Set where
    cheat : Oops -> Cheat

  data Oops : Set where
    oops : (Cheat -> Cheat) -> Oops

