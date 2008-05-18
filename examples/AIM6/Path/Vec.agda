
module Vec where

open import Star
open import Nat

data Step (A : Set) : Nat -> Nat -> Set where
  step : (x : A){n : Nat} -> Step A (suc n) n

Vec : (A : Set) -> Nat -> Set
Vec A n = Star (Step A) n zero

[] : {A : Set} -> Vec A zero
[] = ε

_::_ : {A : Set}{n : Nat} -> A -> Vec A n -> Vec A (suc n)
x :: xs = step x • xs

_+++_ : {A : Set}{n m : Nat} -> Vec A n -> Vec A m -> Vec A (n + m)
_+++_ {A}{m = m} xs ys = map +m step+m xs ++ ys
  where
    +m = \z -> z + m
    step+m : Step A =[ +m ]=> Step A
    step+m (step x) = step x

vec : {A : Set}{n : Nat} -> A -> Vec A n
vec {n = ε}     x = []
vec {n = _ • n} x = x :: vec x

_⊗_ : {A B : Set}{n : Nat} -> Vec (A -> B) n -> Vec A n -> Vec B n
ε             ⊗ ε             = []
(step f • fs) ⊗ (step x • xs) = f x :: (fs ⊗ xs)
ε             ⊗ (() • _)

{- Some proof about _-_ needed...

vreverse : {A : Set}{n : Nat} -> Vec A n -> Vec A n
vreverse {A}{n} xs = {! !} -- map i f (reverse xs)
  where
    i : Nat -> Nat
    i m = n - m

    f : Step A op =[ i ]=> Step A
    f (step x) = {! !} -- step x
-}