
module Lib.List where

open import Lib.Prelude
open import Lib.Id

infix  30 _∈_
infixr 40 _::_ _++_
infix  45 _!_

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

{-# COMPILED_DATA List [] [] (:) #-}
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _::_ #-}

_++_ : {A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f z [] = z
foldr f z (x :: xs) = f x (foldr f z xs)

map : {A B : Set} -> (A -> B) -> List A -> List B
map f [] = []
map f (x :: xs) = f x :: map f xs

map-id : forall {A}(xs : List A) -> map id xs ≡ xs
map-id [] = refl
map-id (x :: xs) with map id xs | map-id xs
... | .xs | refl = refl

data _∈_ {A : Set} : A -> List A -> Set where
  hd : forall {x xs}   ->           x ∈ x :: xs
  tl : forall {x y xs} -> x ∈ xs -> x ∈ y :: xs

data All {A : Set}(P : A -> Set) : List A -> Set where
  []   : All P []
  _::_ : forall {x xs} -> P x -> All P xs -> All P (x :: xs)

head : forall {A}{P : A -> Set}{x xs} -> All P (x :: xs) -> P x
head (x :: xs) = x

tail : forall {A}{P : A -> Set}{x xs} -> All P (x :: xs) -> All P xs
tail (x :: xs) = xs

_!_ : forall {A}{P : A -> Set}{x xs} -> All P xs -> x ∈ xs -> P x
xs ! hd   = head xs
xs ! tl n = tail xs ! n

tabulate : forall {A}{P : A -> Set}{xs} -> ({x : A} -> x ∈ xs -> P x) -> All P xs
tabulate {xs = []}      f = [] 
tabulate {xs = x :: xs} f = f hd :: tabulate (f ∘ tl)

mapAll : forall {A B}{P : A -> Set}{Q : B -> Set}{xs}(f : A -> B) ->
         ({x : A} -> P x -> Q (f x)) -> All P xs -> All Q (map f xs)
mapAll f h [] = []
mapAll f h (x :: xs) = h x :: mapAll f h xs

mapAll- : forall {A}{P Q : A -> Set}{xs} ->
          ({x : A} -> P x -> Q x) -> All P xs -> All Q xs
mapAll- {xs = xs} f zs with map id xs | map-id xs | mapAll id f zs
... | .xs | refl | r = r

infix 20 _⊆_

data _⊆_ {A : Set} : List A -> List A -> Set where
  stop : [] ⊆ []
  drop : forall {xs y ys} -> xs ⊆ ys -> xs ⊆ y :: ys
  keep : forall {x xs ys} -> xs ⊆ ys -> x :: xs ⊆ x :: ys

⊆-refl : forall {A}{xs : List A} -> xs ⊆ xs
⊆-refl {xs = []}      = stop
⊆-refl {xs = x :: xs} = keep ⊆-refl

_∣_ : forall {A}{P : A -> Set}{xs ys} -> All P ys -> xs ⊆ ys -> All P xs
[]        ∣ stop   = []
(x :: xs) ∣ drop p = xs ∣ p
(x :: xs) ∣ keep p = x :: (xs ∣ p)
