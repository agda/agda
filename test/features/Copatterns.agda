{-# OPTIONS --copatterns #-}

module Copatterns where

record Stream (A : Set) : Set where
  field
    head : A
    tail : Stream A
open Stream

repeat : {A : Set}(a : A) -> Stream A
head (repeat a) = a
tail (repeat a) = repeat a

map : {A B : Set}(f : A -> B)(as : Stream A) -> Stream B
head (map f as) = f (head as)
tail (map f as) = map f (tail as)

iterate : {A : Set}(f : A -> A)(a : A) -> Stream A
head (iterate f a) = a
tail (iterate f a) = iterate f (f a)

scanl : {A B : Set} -> (B -> A -> B) -> B -> Stream A -> Stream B
head (scanl f b as) = b
tail (scanl f b as) = scanl f (f b (head as)) (tail as)

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

nats : Stream Nat
nats = iterate suc zero

alternate : Stream Nat
(      head alternate ) = zero
(head (tail alternate)) = suc zero
(tail (tail alternate)) = alternate

record _×_ (A B : Set) : Set where
  field
    fst : A
    snd : B
open _×_

build : {A S : Set} → (S → A × S) -> S -> Stream A
head (build step s) = fst (step s)
tail (build step s) = build step (snd (step s))
-- build step s = mapSnd (build step) (step s)

build1 : {A S : Set} → (S → A × S) -> S -> Stream A
build1 step s = record 
  { head = fst (step s)
  ; tail = build1 step (snd (step s))
  }

build2 : {A S : Set} → (S → A × S) -> S -> Stream A
build2 step s = record 
  { head = fst p
  ; tail = build2 step (snd p)
  }
  where p = step s


mapSnd : {A B C : Set}(f : B → C) → A × B → A × C
fst (mapSnd f p) = fst p
snd (mapSnd f p) = f (snd p) 

record Str (A : Set) : Set where
  field
    out : A × Str A
open Str

build' : {A S : Set} → (S → A × S) -> S -> Stream A
out (build' step s) = mapSnd (build' step) (step s)
