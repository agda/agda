
module Prelude where

infixr 90 _∘_
infixr 0 _$_

id : {A : Set} -> A -> A
id x = x

_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
(f ∘ g) x = f (g x)

_$_ : {A B : Set} -> (A -> B) -> A -> B
f $ x = f x

flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f x y = f y x

const : {A B : Set} -> A -> B -> A
const x _ = x

typeOf : {A : Set} -> A -> Set
typeOf {A} _ = A

typeOf1 : {A : Set1} -> A -> Set1
typeOf1 {A} _ = A

