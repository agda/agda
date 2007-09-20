
module Lib.Vec where

open import Lib.Nat

infixr 40 _►_

data Vec (A : Set) : Nat -> Set where
  ε   : Vec A 0
  _►_ : forall {n} -> A -> Vec A n -> Vec A (suc n)
