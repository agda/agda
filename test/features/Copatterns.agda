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
