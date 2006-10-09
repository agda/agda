
module PiInSet where

Rel : Set -> Set1
Rel A = A -> A -> Prop

Reflexive : {A:Set} -> Rel A -> Prop
Reflexive {A} _R_ = forall x -> x R x

Symmetric : {A:Set} -> Rel A -> Prop
Symmetric {A} _R_ = forall x y -> x R y -> y R x

data True : Prop where
  tt : True

data False : Prop where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_==_ : Rel Nat
zero  == zero  = True
zero  == suc _ = False
suc _ == zero  = False
suc n == suc m = n == m

refl== : Reflexive _==_
refl==  zero   = tt
refl== (suc n) = refl== n

sym== : Symmetric _==_
sym==  zero    zero   tt = tt
sym==  zero   (suc _) ()
sym== (suc _)  zero   ()
sym== (suc n) (suc m) n==m = sym== n m n==m

