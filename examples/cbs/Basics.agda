
module Basics where

data   False : Set where
record True  : Set where

tt : True
tt = _

¬_ : Set -> Set
¬ A = A -> False

data Lift (A : Set) : Set where
  bot  : Lift A
  lift : A -> Lift A

data LR : Set where
  left  : LR
  right : LR

_=<<_ : {A B : Set} -> (A -> Lift B) -> Lift A -> Lift B
f =<< bot    = bot
f =<< lift v = f v

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

infix 10 _==_

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

_%_ : {A B : Set}{C : B -> Set}
      (f : (x : B) -> C x)(g : A -> B)(x : A) -> C (g x)
f % g = \x -> f (g x)

infixr 50 _::_

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

data Bool : Set where
  true  : Bool
  false : Bool

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y