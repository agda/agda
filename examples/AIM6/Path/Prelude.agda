
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

tt : True
tt = _

! : {A : Set} -> A -> True
! = _

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

subst : {A : Set}(P : A -> Set){x y : A} -> x == y -> P y -> P x
subst P refl p = p

cong : {A B : Set}(f : A -> B){x y : A} -> x == y -> f x == f y
cong f refl = refl

sym : {A : Set}{x y : A} -> x == y -> y == x
sym refl = refl

trans : {A : Set}{x y z : A} -> x == y -> y == z -> x == z
trans refl yz = yz

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

infixr 10 _,_

record Σ (A : Set)(B : A -> Set) : Set where
  field
    fst : A
    snd : B fst

_,,_ : {A : Set}{B : A -> Set}(x : A) -> B x -> Σ A B
x ,, y = record { fst = x; snd = y }

private module Σp {A : Set}{B : A -> Set} = Σ {A}{B}
open Σp public

data _∨_ (A B : Set) : Set where
  inl : A -> A ∨ B
  inr : B -> A ∨ B

data Bool : Set where
  false : Bool
  true  : Bool

IsTrue : Bool -> Set
IsTrue false = False
IsTrue true  = True

IsFalse : Bool -> Set
IsFalse true  = False
IsFalse false = True

data Inspect (b : Bool) : Set where
  itsTrue  : IsTrue b -> Inspect b
  itsFalse : IsFalse b -> Inspect b

inspect : (b : Bool) -> Inspect b 
inspect true  = itsTrue  _
inspect false = itsFalse _

data LeqBool : Rel Bool where
  ref : {b : Bool} -> LeqBool b b
  up  : LeqBool false true

One : Rel True
One _ _ = True

_[×]_ : {A B : Set} -> Rel A -> Rel B -> Rel (A × B)
(R [×] S) (a₁ , b₁) (a₂ , b₂) = R a₁ a₂ × S b₁ b₂
