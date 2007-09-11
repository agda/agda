
module Prelude where

infix 20 _≡_ _≤_ _∈_
infixl 60 _,_ _++_ _+_ _◄_ _◄²_

_∘_ : {A B : Set}{C : B -> Set}(f : (x : B) -> C x)(g : A -> B)(x : A) -> C (g x)
(f ∘ g) x = f (g x)

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

data All {A : Set}(P : A -> Set) : List A -> Set where
  ∅   : All P ε
  _◄_ : forall {xs x} -> All P xs -> P x -> All P (xs , x)

{-
data Some {A : Set}(P : A -> Set) : List A -> Set where
  hd : forall {x xs} -> P x -> Some P (xs , x)
  tl : forall {x xs} -> Some P xs -> Some P (xs , x)
-}

data _∈_ {A : Set}(x : A) : List A -> Set where
  hd : forall {xs} -> x ∈ xs , x
  tl : forall {y xs} -> x ∈ xs -> x ∈ xs , y

_!_ : {A : Set}{P : A -> Set}{xs : List A} ->
      All P xs -> {x : A} -> x ∈ xs -> P x
∅        ! ()
(xs ◄ x) ! hd   = x
(xs ◄ x) ! tl i = xs ! i

tabulate : {A : Set}{P : A -> Set}{xs : List A} ->
           ({x : A} -> x ∈ xs -> P x) -> All P xs
tabulate {xs = ε}      f = ∅
tabulate {xs = xs , x} f = tabulate (f ∘ tl) ◄ f hd

data All² {I : Set}{A : I -> Set}(P : {i : I} -> A i -> Set) :
          {is : List I} -> All A is -> Set where
  ∅²   : All² P ∅
  _◄²_ : forall {i is}{x : A i}{xs : All A is} ->
         All² P xs -> P x -> All² P (xs ◄ x)

data _∈²_ {I : Set}{A : I -> Set}{i : I}(x : A i) :
          {is : List I} -> All A is -> Set where
  hd² : forall {is}{xs : All A is} -> x ∈² xs ◄ x
  tl² : forall {j is}{y : A j}{xs : All A is} ->
        x ∈² xs -> x ∈² xs ◄ y
