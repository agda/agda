module ModuleReexport where

open import Common.Unit
open import Common.Nat
open import Common.IO

module A (B : Set) (b : B) where
  data X : Set where
    Con1 : B -> X
    Con2 : X
  f : X -> B
  f (Con1 x) = x
  f Con2 = b


module X = A Nat 10


main = printNat (A.f Nat 10 (X.Con1 20)) ,,
  putStrLn "" ,,
  printNat (A.f Nat 10 X.Con2) ,,
  putStrLn "" ,,
  return unit
