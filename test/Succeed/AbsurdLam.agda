
module AbsurdLam where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Fin : Nat -> Set where
  fzero : forall {n} -> Fin (suc n)
  fsuc  : forall {n} -> Fin n -> Fin (suc n)

data False : Set where

elimFalse : (A : Set) -> False -> A
elimFalse A = \()

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

magic : forall {n} -> suc n == zero -> False
magic = \()

hidden : Nat -> {x : Fin zero} -> False
hidden = \n {}
