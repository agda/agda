module Path where

id : {A : Set} -> A -> A
id x = x

_·_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
f · g = \ x -> f (g x)

Rel : Set -> Set1
Rel X = X -> X -> Set

record True : Set where

! : {A : Set} -> A -> True
! = _

data Star {X : Set} (R : Rel X) : Rel X where
  ε   : {x : X} -> Star R x x
  _•_ : {x y z : X} -> R x y -> Star R y z -> Star R x z

_++_ : {X : Set}{R : Rel X}{x y z : X} ->
       Star R x y -> Star R y z -> Star R x z
ε        ++ ys  =  ys
(x • xs) ++ ys  =  x • (xs ++ ys)

_=>_ : {X : Set} -> Rel X -> Rel X -> Set
R => S = forall {a b} -> R a b -> S a b

_on_ : {X Y : Set} -> (R : Rel X) -> (f : Y -> X) -> Rel Y
R on f = \a b -> R (f a) (f b)

_=[_]=>_ : {X Y : Set} (R : Rel X) (f : X -> Y) (S : Rel Y) -> Set
R =[ f ]=> S = R => (S on f)

join : {X : Set}{R : Rel X} -> Star (Star R) => Star R
join ε           =  ε
join (xs • xss)  =  xs ++ join xss

return : {X : Set}{R : Rel X} -> R => Star R
return x = x • ε

map : forall {X Y R S} -> (f : X -> Y) ->
      R =[ f ]=> S  ->  Star R =[ f ]=> Star S
map f pm ε         =  ε
map f pm (x • xs)  =  pm x • map f pm xs

bind : forall {X Y R S} -> (f : X -> Y) ->
       R =[ f ]=> Star S  ->  Star R =[ f ]=> Star S
bind f k m = join (map f k m)

bind' : forall {X Y R S} -> (f : X -> Y) ->
        R =[ f ]=> Star S  ->  Star R =[ f ]=> Star S
bind' f k ε         =  ε
bind' f k (x • xs)  =  k x ++ bind' f k xs

join' : {X : Set}{R : Rel X} -> Star (Star R) => Star R
join' = bind' id id

map' : forall {X Y R S} -> (f : X -> Y) ->
       R =[ f ]=> S  ->  Star R =[ f ]=> Star S
map' f k = bind' f (return · k)

One : Rel True
One _ _ = True

length : {X : Set}{R : Rel X} -> Star R =[ ! ]=> Star One
length = map ! !

-- Natural number stuff

Nat : Set
Nat = Star One _ _

zero : Nat
zero = ε

suc : Nat -> Nat
suc n = _ • n

_+_ : Nat -> Nat -> Nat
_+_ = _++_

_*_ : Nat -> Nat -> Nat
x * y = bind id (\ _ -> y) x

-- {-# BUILTIN NATURAL  Nat  #-}
-- {-# BUILTIN ZERO     zero #-}
-- {-# BUILTIN SUC      suc  #-}
-- {-# BUILTIN NATPLUS  _+_  #-}
-- {-# BUILTIN NATTIMES _*_  #-}

-- {-# BUILTIN NATPLUS  _++_ #-}  This gave :agda: src/full/TypeChecking/Primitive.hs:(238,135)-(243,25): Non-exhaustive patterns in lambda


test : Nat
test = suc (suc zero) ++ suc (suc zero)  -- does not evaluate to 4

-- Lists

[_] : Set -> Rel True
[ A ] = \_ _ -> A

List : Set -> Set
List A = Star [ A ] _ _

-- Vectors

data Step (A : Set) : Nat -> Nat -> Set where
  step : (x : A){n : Nat} -> Step A (suc n) n

Vec : (A : Set) -> Nat -> Set
Vec A n = Star (Step A) n zero

[] : {A : Set} -> Vec A zero
[] = ε

_::_ : {A : Set}{n : Nat} -> A -> Vec A n -> Vec A (suc n)
x :: xs = step x • xs
