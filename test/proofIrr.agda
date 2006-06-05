
module proofIrr where

data True : Prop where
  tt : True

-- not allowed with proof irrelevance
data (\/) (P,Q:Prop) : Prop where
  inl : P -> P \/ Q
  inr : Q -> P \/ Q

foo : {P:Prop} -> (F : P -> Set) -> (p,q:P) -> F p -> F q
foo F p q fp = fp

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Bool : Set where
  false : Bool
  true  : Bool

bad : True \/ True -> Set
bad (inl tt) = Nat
bad (inr tt) = Bool

