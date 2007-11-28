
module Basics where

_%_ : {A B : Set}{C : B -> Set}
      (f : (x : B) -> C x)(g : A -> B)(x : A) -> C (g x)
f % g = \x -> f (g x)

-- Logic

data   False : Set where
record True  : Set where

tt : True
tt = _

¬_ : Set -> Set
¬ A = A -> False

record ∃ {A : Set}(P : A -> Set) : Set where
  field
    witness : A
    proof   : P witness

∃-intro : {A : Set}{P : A -> Set}(x : A) -> P x -> ∃ P
∃-intro x p = record { witness = x; proof = p }

infixr 15 _/\_ _×_

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

_/\_ = _×_

-- Maybe

data Lift (A : Set) : Set where
  bot  : Lift A
  lift : A -> Lift A

_=<<_ : {A B : Set} -> (A -> Lift B) -> Lift A -> Lift B
f =<< bot    = bot
f =<< lift v = f v

-- Nat

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- Identity

infix 10 _==_

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data Id {A : Set}(x : A) : Set where
  it : (y : A) -> x == y -> Id x

-- Booleans

data Bool : Set where
  true  : Bool
  false : Bool

data LR : Set where
  left  : LR
  right : LR

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y

-- Lists

infixr 50 _::_

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

data Elem {A : Set}(x : A) : List A -> Set where
  hd : forall {xs} -> Elem x (x :: xs)
  tl : forall {y xs} -> Elem x xs -> Elem x (y :: xs)
