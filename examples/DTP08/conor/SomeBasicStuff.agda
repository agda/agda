
-- Some basic stuff for Conor's talk.
module SomeBasicStuff where

infixr 40 _::_ _↦_∣_
infix 30 _∈_ _==_
infixr 10 _,_

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data Σ (A : Set)(B : A -> Set) : Set where
  _,_ : (x : A) -> B x -> Σ A B

_×_ : Set -> Set -> Set
A × B = Σ A \_ -> B

fst : {A : Set}{B : A -> Set} -> Σ A B -> A
fst (x , y) = x

snd : {A : Set}{B : A -> Set}(p : Σ A B) -> B (fst p)
snd (x , y) = y

data   False : Set where
record True  : Set where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data [_] (A : Set) : Set where
  []   : [ A ]
  _::_ : A -> [ A ] -> [ A ]

data _∈_ {A : Set} : A -> [ A ] -> Set where
  zero : forall {x xs} -> x ∈ x :: xs
  suc  : forall {x y xs} -> x ∈ xs -> x ∈ y :: xs

postulate Tag : Set
{-# BUILTIN STRING Tag #-}

Enumeration = [ Tag ]

data Enum (ts : Enumeration) : Set where
  enum : (t : Tag) -> t ∈ ts -> Enum ts

data Table (A : Set1) : Enumeration -> Set1 where
  []    : Table A []
  _↦_∣_ : forall {ts} -> (t : Tag) -> A -> Table A ts ->
          Table A (t :: ts)

lookup : forall {A ts} -> Table A ts -> Enum ts -> A
lookup []             (enum _ ())
lookup (.t ↦ v ∣ tbl) (enum t zero)    = v
lookup (_  ↦ v ∣ tbl) (enum t (suc p)) = lookup tbl (enum t p)
