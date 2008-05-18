
module Trans where

open import Prelude

Rel : Set -> Set1
Rel A = A -> A -> Set

data [_]* {A : Set}(R : Rel A)(x : A) : A -> Set where
  ref : [ R ]* x x
  _▹_ : {y z : A} -> R x y -> [ R ]* y z -> [ R ]* x z

infixr 40 _▹_ _▹◃_

length : {A : Set}{R : Rel A}{x y : A} -> [ R ]* x y -> Nat
length ref      = zero
length (x ▹ xs) = suc (length xs)

_=[_]=>_ : {A B : Set}(R : Rel A)(i : A -> B)(S : Rel B) -> Set
R =[ i ]=> S = forall {x y} -> R x y -> S (i x) (i y)

map : {A B : Set}{R : Rel A}{S : Rel B}(i : A -> B) ->
      (R =[ i ]=> S) ->
      {x y : A} -> [ R ]* x y -> [ S ]* (i x) (i y)
map i f ref      = ref
map i f (x ▹ xs) = f x ▹ map i f xs

lem-length-map :
      {A B : Set}{R : Rel A}{S : Rel B}(i : A -> B)
      (f : R =[ i ]=> S){x y : A}(xs : [ R ]* x y) ->
      length xs ≡ length (map {S = S} i f xs)
lem-length-map i f ref      = refl
lem-length-map i f (x ▹ xs) = cong suc (lem-length-map i f xs)

_▹◃_ : {A : Set}{R : Rel A}{x y z : A} ->
       [ R ]* x y -> [ R ]* y z -> [ R ]* x z
ref      ▹◃ ys = ys
(x ▹ xs) ▹◃ ys = x ▹ (xs ▹◃ ys)

lem-length▹◃ : {A : Set}{R : Rel A}{x y z : A}
               (r₁ : [ R ]* x y)(r₂ : [ R ]* y z) ->
               length r₁ + length r₂ ≡ length (r₁ ▹◃ r₂)
lem-length▹◃ ref      ys = refl
lem-length▹◃ (x ▹ xs) ys = cong suc (lem-length▹◃ xs ys)
