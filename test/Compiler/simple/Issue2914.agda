
open import Agda.Builtin.IO
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit

private
  n : Nat
  n = 7

{-# COMPILE GHC n as n #-}

postulate
  main : IO ⊤

{-# COMPILE GHC main = print n #-}
