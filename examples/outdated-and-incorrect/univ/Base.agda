
module Base where

data True : Set where
  T : True

data False : Set where

infix 20 _*_

data _*_ (A : Set)(B : A -> Set) : Set where
 <_,_> : (x : A) -> B x -> A * B

rel : Set -> Set1 
rel A = A -> A -> Set

pred : Set -> Set1 
pred A = A -> Set

Refl : {A : Set} -> rel A -> Set
Refl {A} R = {x : A} -> R x x 

Sym : {A : Set} -> rel A -> Set
Sym {A} R = {x y : A} -> R x y -> R y x

Trans : {A : Set} -> rel A -> Set
Trans {A} R = {x y z : A} -> R x y -> R y z -> R x z

Map : {A : Set} -> rel A -> {B : Set} -> rel B -> pred (A -> B)
Map {A} _R_ _S_ f = {x y : A} -> x R y -> f x S f y

