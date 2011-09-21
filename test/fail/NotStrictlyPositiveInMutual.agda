
module NotStrictlyPositiveInMutual where

mutual
  data Oops : Set

  data Cheat : Set where
    cheat : Oops -> Cheat

  data Oops where
    oops : (Cheat -> Cheat) -> Oops

