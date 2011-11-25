module FlexInterpreter where

data Ty : Set where
  nat : Ty
  arr : Ty -> Ty -> Ty

data Exp : Ty -> Set where
  zero : Exp nat
  suc  : Exp (arr nat nat)
  pred : Exp (arr nat nat)
  app  : {a b : Ty} -> Exp (arr a b) -> Exp a -> Exp b

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

Sem : Ty -> Set
Sem nat = Nat
Sem (arr a b) = Sem a -> Sem b

eval : {a : Ty} -> Exp a -> Sem a
eval zero = zero
eval suc  = suc
eval pred zero = zero
eval pred (suc n) = n
eval (app f e) = eval f (eval e)
