
module Prelude where

id : {A : Set} -> A -> A
id x = x

_·_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
f · g = \ x -> f (g x)

flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f x y = f y x

Rel : Set -> Set1
Rel X = X -> X -> Set

data False : Set where
record True : Set where

! : {A : Set} -> A -> True
! = _

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

infixr 10 _,_

data Bool : Set where
  false : Bool
  true  : Bool

data LeqBool : Rel Bool where
  ref : {b : Bool} -> LeqBool b b
  up  : LeqBool false true

One : Rel True
One _ _ = True

_[×]_ : {A B : Set} -> Rel A -> Rel B -> Rel (A × B)
(R [×] S) (a₁ , b₁) (a₂ , b₂) = R a₁ a₂ × S b₁ b₂
