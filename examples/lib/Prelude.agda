
module Prelude where

id : {A : Set} -> A -> A
id x = x

infixr 90 _∘_
_∘_ : {A, B, C : Set} -> (B -> C) -> (A -> B) -> A -> C
(f ∘ g) x = f (g x)

infixr 10 _$_
_$_ : {A, B : Set} -> (A -> B) -> A -> B
f $ x = f x

flip : {A, B, C : Set} -> (A -> B -> C) -> B -> A -> C
flip f x y = f y x

const : {A, B : Set} -> A -> B -> A
const x _ = x

typeOf : {A : Set} -> A -> Set
typeOf {A} _ = A

data _×_ (A, B : Set) : Set where
  <_|_> : A -> B -> A × B

