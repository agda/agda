
module Examples where

open import Prelude
open import Star
open import Modal

El : Set -> Rel True
El A _ _ = A

List : Set -> Set
List A = Star (El A) _ _

Nat = List True

zero : Nat
zero = ε

suc : Nat -> Nat
suc n = _ • n

-- Vectors

Vec : Set -> Nat -> Set
Vec A = All (\_ -> A)

infixr 40 _::_
_::_ : {A : Set}{n : Nat} -> A -> Vec A n -> Vec A (suc n)
x :: xs = check x • xs

-- Fin

Fin : Nat -> Set
Fin = Any (\_ -> True)

-- Turning a vector to a list

vecToList : {A : Set}{n : Nat} -> Vec A n -> List A
vecToList {A} = map (\_ -> _) uncheck

listToVec : {A : Set}(xs : List A) -> Vec A (length xs)
listToVec  ε       = ε
listToVec (x • xs) = x :: listToVec xs

-- span

data SpanView {A : Set}{R : Rel A}(p : {a b : A} -> R a b -> Bool) :
              EdgePred (Star R) where
  oneFalse : {a b c d : A}(xs : Star R a b)(pxs : All (\x -> IsTrue (p x)) xs)
             (x : R b c)(¬px : IsFalse (p x))(ys : Star R c d) ->
             SpanView p (xs ++ x • ys)
  allTrue  : {a b : A}{xs : Star R a b}(ts : All (\x -> IsTrue (p x)) xs) ->
             SpanView p xs

span : {A : Set}{R : Rel A}(p : {a b : A} -> R a b -> Bool){a b : A}
       (xs : Star R a b) -> SpanView p xs
span p ε = allTrue ε
span p (x • xs) with inspect (p x)
span p (x • xs) | itsFalse ¬px = oneFalse ε ε x ¬px xs
span p (x • xs) | itsTrue px with span p xs
span p (x • .(xs ++ y • ys)) | itsTrue px
     | oneFalse xs pxs y ¬py ys =
       oneFalse (x • xs) (check px • pxs) y ¬py ys
span p (x • xs) | itsTrue px | allTrue pxs =
       allTrue (check px • pxs)

test : Vec Nat (suc (suc (suc zero)))
test = zero :: suc zero :: suc (suc zero) :: ε
