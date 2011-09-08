
module Issue451 where

infix 10 _==_
data _==_ {A : Set} (x : A) : (y : A) -> Set where
 refl : x == x

postulate
 Nat : Set

data G : Nat -> Nat -> Set where
 I : (place : Nat) -> G place place
 s : (n m : Nat) -> G n m

mul : (l m n : Nat) -> G m n -> G l m -> G l n
mul a b .b (I .b)   x         = x
mul a .a b x        (I .a)    = x
mul a b c (s .b .c) (s .a .b) = s a c

postulate
  a b c : Nat
  f : G a b

bad : mul a a b (s a b) (I a) == s a b
bad = refl
