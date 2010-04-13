
module Simple where

data Nat : Set where
  z : Nat
  s : Nat → Nat

data Exp : Set where
  val : Nat → Exp
  throw : Exp

data Maybe (A : Set) : Set where
  Just    : A → Maybe A
  Nothing : Maybe A

eval : Exp → Maybe Nat
eval (val n)        = ?
eval throw          = {!!}
