
module test where

id : {A:Set} -> A -> A
id x = x

foo : {A:Set} -> A -> A -> {!!}
foo x y = id ?

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

bar : Nat -> Nat
bar n @ (suc m) = n + m
bar zero      = suc zero

infixr 12 _++_  _::_

data List (A:Set) : Set where
  nil  : List A
  _::_ : A -> List A -> List A

_++_ : {A:Set} -> List A -> List A -> List A
nil ++ ys = ys
(x::xs) ++ ys = x :: (xs ++ ys)

baz : {A:Set} -> List A -> List A
baz xs @ (_ :: ys @ (_ :: zs)) = xs ++ ys ++ zs
baz xs @ (x :: nil)	   = x :: xs
baz nil			   = nil

postulate
  T : Nat -> Set
  mkT : (n:Nat) -> T n

f : (n:Nat) -> T n -> T n
f n @ (suc _) t = mkT n
f zero	      t = t

foo_ : Nat -> Nat
foo_ n = n

beta : Nat -> Nat
beta n = (\x -> x) n

g : Nat -> Nat
g n = let f = \z -> n + suc z
      in  f (f n)

id' : Nat -> {A:Set} -> A -> A
id' = \_ -> id {_}

