
module Star where

open import Prelude

infixr 40 _•_ _++_
infixl 30 _on_
infixr 20 _==>_ _=[_]=>_

data Star {X : Set} (R : Rel X) : Rel X where
  ε   : {x : X} -> Star R x x
  _•_ : {x y z : X} -> R x y -> Star R y z -> Star R x z

_++_ : {X : Set}{R : Rel X}{x y z : X} ->
       Star R x y -> Star R y z -> Star R x z
ε        ++ ys  =  ys
(x • xs) ++ ys  =  x • (xs ++ ys)

_==>_ : {X : Set} -> Rel X -> Rel X -> Set
R ==> S = forall {a b} -> R a b -> S a b

_on_ : {X Y : Set} -> (R : Rel X) -> (f : Y -> X) -> Rel Y
R on f = \a b -> R (f a) (f b)

_=[_]=>_ : {X Y : Set} (R : Rel X) (f : X -> Y) (S : Rel Y) -> Set
R =[ f ]=> S = R ==> S on f

return : {X : Set}{R : Rel X} -> R ==> Star R
return x = x • ε

module JoinMap where

  join : {X : Set}{R : Rel X} -> Star (Star R) ==> Star R
  join ε           =  ε
  join (xs • xss)  =  xs ++ join xss

  map : forall {X Y R S} -> (f : X -> Y) ->
        R =[ f ]=> S  ->  Star R =[ f ]=> Star S
  map f pm ε         =  ε
  map f pm (x • xs)  =  pm x • map f pm xs

  bind : forall {X Y R S} -> (f : X -> Y) ->
         R =[ f ]=> Star S  ->  Star R =[ f ]=> Star S
  bind f k m = join (map f k m)

bind : forall {X Y R S} -> (f : X -> Y) ->
        R =[ f ]=> Star S  ->  Star R =[ f ]=> Star S
bind f k ε         =  ε
bind f k (x • xs)  =  k x ++ bind f k xs

join : {X : Set}{R : Rel X} -> Star (Star R) ==> Star R
join = bind id id

map : forall {X Y R S} -> (f : X -> Y) ->
       R =[ f ]=> S  ->  Star R =[ f ]=> Star S
map f k = bind f (return · k)

-- Generic length

length : {X : Set}{R : Rel X} -> Star R =[ ! ]=> Star One
length = map ! !

-- Reverse

_op : {X : Set} -> Rel X -> Rel X
(R op) a b = R b a

reverse : {X : Set}{R : Rel X}{a b : X} -> Star R a b -> Star (R op) b a
reverse {X}{R} xs = rev xs ε
  where
    rev : forall {a b c} ->
          Star R a b -> Star (R op) a c -> Star (R op) b c
    rev ε ys = ys
    rev (x • xs) ys = rev xs (x • ys)
