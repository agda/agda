
module MagicWith where

data _×_ (A : Set)(B : A -> Set) : Set where
  _,_ : (x : A) -> B x -> A × B

fst : {A : Set}{B : A -> Set} -> A × B -> A
fst (x , y) = x

snd : {A : Set}{B : A -> Set}(p : A × B) -> B (fst p)
snd (x , y) = y

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

record True  : Set where
data   False : Set where

IsZero : Nat -> Set
IsZero zero    = True
IsZero (suc _) = False

Uncurry : {A : Set}{B : A -> Set} -> ((x : A) -> B x -> Set) -> A × B -> Set
Uncurry F p = F (fst p) (snd p)

F : (n : Nat) -> IsZero n -> Set
F zero _ = True
F (suc _) ()

-- Trying to match only on fst p will give a (bad) error,
-- just as it should.
f : (p : Nat × IsZero) -> Uncurry F p
f p with fst p | snd p
f p | zero  | q = _
f p | suc _ | ()