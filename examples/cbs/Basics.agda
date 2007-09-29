
module Basics where

data   False : Set where
record True  : Set where

tt : True
tt = _

kill : False -> {A : Set} -> A
kill ()

data _\/_ (A B : Set) : Set where
  inl : A -> A \/ B
  inr : B -> A \/ B

¬_ : Set -> Set
¬ A = A -> False

data ∃ (A : Set)(P : A -> Set) : Set where
  _,_ : (x : A) -> P x -> ∃ A P

data Lift (A : Set) : Set where
  ⊥    : Lift A
  lift : A -> Lift A

data LR : Set where
  left  : LR
  right : LR

_=<<_ : {A B : Set} -> (A -> Lift B) -> Lift A -> Lift B
f =<< ⊥      = ⊥
f =<< lift v = f v

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

infix 10 _==_

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

_∘_ : {A B : Set}{C : B -> Set}
      (f : (x : B) -> C x)(g : A -> B)(x : A) -> C (g x)
f ∘ g = \x -> f (g x)