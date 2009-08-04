
module Vec where

import Nat
import Fin

open Nat hiding (_==_; _<_)
open Fin

data Nil : Set where
  vnil : Nil

data Cons (A As : Set) : Set where
  vcons : A -> As -> Cons A As

mutual
  Vec' : Nat -> Set -> Set
  Vec' zero    A = Nil
  Vec' (suc n) A = Cons A (Vec n A)

  data Vec (n : Nat)(A : Set) : Set where
    vec : Vec' n A -> Vec n A

ε : {A : Set} -> Vec zero A
ε = vec vnil

_∷_ : {A : Set}{n : Nat} -> A -> Vec n A -> Vec (suc n) A
x ∷ xs = vec (vcons x xs)

_!_ : {n : Nat}{A : Set} -> Vec n A -> Fin n -> A
_!_ {zero}   _                 (fin ())
_!_ {suc n} (vec (vcons x xs)) (fin fz)     = x
_!_ {suc n} (vec (vcons x xs)) (fin (fs i)) = xs ! i

map : {n : Nat}{A B : Set} -> (A -> B) -> Vec n A -> Vec n B
map {zero}  f (vec vnil)         = ε
map {suc n} f (vec (vcons x xs)) = f x ∷ map f xs

fzeroToN-1 : (n : Nat) -> Vec n (Fin n)
fzeroToN-1 zero    = ε
fzeroToN-1 (suc n) = fzero ∷ map fsuc (fzeroToN-1 n)

