
module test where

id : {A:Set} -> A -> A
id x = x

foo : {A:Set} -> A -> A -> {!!}
foo x y = id ?

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

(+) : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

bar : Nat -> Nat
bar n@(suc m) = n + m
bar zero      = suc zero

infixr 12 ++, ::

data List (A:Set) : Set where
  nil  : List A
  (::) : A -> List A -> List A

(++) : {A:Set} -> List A -> List A -> List A
nil ++ ys = ys
(x::xs) ++ ys = x :: (xs ++ ys)

baz : {A:Set} -> List A -> List A
baz xs@(_ :: ys@(_ :: zs)) = xs ++ ys ++ zs
baz xs@(x :: nil)	   = x :: xs
baz nil			   = nil

postulate
  T : Nat -> Set
  mkT : (n:Nat) -> T n

f : (n:Nat) -> T n -> T n
f n@(suc _) t = mkT n
f zero	    t = t

