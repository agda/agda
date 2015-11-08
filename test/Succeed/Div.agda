
module Div where

data True : Set where
  trivial : True

data False : Set where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

NonZero : Nat -> Set
NonZero  zero   = False
NonZero (suc _) = True

divHelp : Nat -> Nat -> Nat -> Nat
divHelp  zero    zero   c = suc zero
divHelp  zero   (suc y) c = zero
divHelp (suc x)  zero   c = suc (divHelp x c c)
divHelp (suc x) (suc y) c = divHelp x y c

div : (x y : Nat) -> NonZero y -> Nat
div  x       zero  ()
div  zero   (suc y) _ = zero
div (suc x) (suc y) _ = divHelp (suc x) (suc y) y

n1 = suc zero
n2 = suc n1
n3 = suc n2
n4 = suc n3
n5 = suc n4
n6 = suc n5
n7 = suc n6
n8 = suc n7
n9 = suc n8
n10 = suc n9
n11 = suc n10
n12 = suc n11

