-- Simple test to check if constraint solving for injective
-- functions is working.
module Injectivity where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}
{-# BUILTIN NATPLUS _+_  #-}

infixr 40 _::_
data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f z []        = z
foldr f z (x :: xs) = f x (foldr f z xs)

data U : Set where
  nat  : U
  list : U -> U

El : U -> Set
El nat      = Nat
El (list a) = List (El a)

sum : {a : U} -> El a -> Nat
sum {nat}    n  = n
sum {list a} xs = foldr (\a b -> sum a + b) zero xs

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

test₁ = sum (1 :: 2 :: 3 :: [])

ok₁ : test₁ == 6
ok₁ = refl

test₂ = sum ((1 :: []) :: (3 :: 5 :: []) :: [])

ok₂ : test₂ == 9
ok₂ = refl

