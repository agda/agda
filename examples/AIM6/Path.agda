module Path where

Rel : Set -> Set1
Rel X = X -> X -> Set

data Star {X : Set} (R : Rel X) : Rel X where
  ε   : {x : X} -> Star R x x
  _•_ : {x y z : X} -> R x y -> Star R y z -> Star R x z

_++_ : forall {X R x y z} -> Star {X} R x y -> Star R y z -> Star R x z
ε ++ ys         =  ys
(x • xs) ++ ys  =  x • (xs ++ ys)

flatten : forall {X R s t} -> Star (Star R) s t -> Star {X} R s t
flatten ε           =  ε
flatten (xs • xss)  =  xs ++ flatten xss

PathMorphism : {X Y : Set} (f : X -> Y) (R : Rel X) (S : Rel Y) -> Set
PathMorphism f R S = forall {a b} -> R a b -> S (f a) (f b)

Map : forall {X Y R S}
    -> (f : X -> Y) -> PathMorphism f R S -> PathMorphism f (Star R) (Star S)
Map f pm ε         =  ε
Map f pm (x • xs)  =  pm x • Map f pm xs

-- Natural numer stuff

record True : Set where

tt : True
tt = _ -- record {}  by the η-law

One : Rel True
One _ _ = True

Nat : Set
Nat = Star One _ _

zero : Nat
zero = ε

suc : Nat -> Nat
suc n = _ • n

_+_ : Nat -> Nat -> Nat
_+_ = _++_

id : {A : Set} -> A -> A
id x = x

_*_ : Nat -> Nat -> Nat
x * y = flatten (Map id (\ _ -> y) x)

{-# BUILTIN NATURAL  Nat  #-}
{-# BUILTIN ZERO     zero #-}
{-# BUILTIN SUC      suc  #-}
{-# BUILTIN NATPLUS  _+_  #-}
{-# BUILTIN NATTIMES _*_  #-}

-- {-# BUILTIN NATPLUS  _++_ #-}  This gave :agda: src/full/TypeChecking/Primitive.hs:(238,135)-(243,25): Non-exhaustive patterns in lambda


test : Nat
test = 2 ++ 2  -- does not evaluate to 4
test2 : Nat
test2 = 2 + 2  -- does     evaluate to 4 (because of the BULTIN)

{-
-}
