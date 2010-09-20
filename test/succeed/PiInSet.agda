
module PiInSet where

Rel : Set -> Set1
Rel A = A -> A -> Set

Reflexive : {A : Set} -> Rel A -> Set
Reflexive {A} _R_ = forall x -> x R x

Symmetric : {A : Set} -> Rel A -> Set
Symmetric {A} _R_ = forall x y -> x R y -> y R x

data True : Set where
  tt : True

data False : Set where

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

