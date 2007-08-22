
module Prelude where

infix 20 _≡_ _≤_
infixl 60 _,_ _++_ _+_

data _≡_ {A : Set}(x : A) : {B : Set} -> B -> Set where
  refl : x ≡ x

cong : {A : Set}{B : A -> Set}(f : (z : A) -> B z){x y : A} ->
       x ≡ y -> f x ≡ f y
cong f refl = refl

subst : {A : Set}(P : A -> Set){x y : A} -> x ≡ y -> P y -> P x
subst P refl px = px

sym : {A : Set}{x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN SUC     suc  #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN NATPLUS _+_  #-}

data _≤_ : Nat -> Nat -> Set where
  leqZ : {m : Nat}   -> zero ≤ m
  leqS : {n m : Nat} -> n ≤ m -> suc n ≤ suc m

refl-≤ : {n : Nat} -> n ≤ n
refl-≤ {zero } = leqZ
refl-≤ {suc n} = leqS refl-≤

refl-≤' : {n m : Nat} -> n ≡ m -> n ≤ m
refl-≤' refl = refl-≤

trans-≤ : {x y z : Nat} -> x ≤ y -> y ≤ z -> x ≤ z
trans-≤ leqZ      yz        = leqZ
trans-≤ (leqS xy) (leqS yz) = leqS (trans-≤ xy yz)

lem-≤suc : {x : Nat} -> x ≤ suc x
lem-≤suc {zero } = leqZ
lem-≤suc {suc x} = leqS lem-≤suc

lem-≤+L : (x : Nat){y : Nat} -> y ≤ x + y
lem-≤+L zero    = refl-≤
lem-≤+L (suc x) = trans-≤ (lem-≤+L x) lem-≤suc

lem-≤+R : {x y : Nat} -> x ≤ x + y
lem-≤+R {zero } = leqZ
lem-≤+R {suc x} = leqS lem-≤+R


data List (A : Set) : Set where
  ε   : List A
  _,_ : List A -> A -> List A

_++_ : {A : Set} -> List A -> List A -> List A
xs ++ ε        = xs
xs ++ (ys , y) = (xs ++ ys) , y
