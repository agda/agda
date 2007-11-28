{-# OPTIONS --no-positivity-check #-}

module Clowns where

import Equality
import Isomorphism
import Derivative
import ChainRule
open import Sets
open import Functor
open import Zipper
open import Dissect

open Functor.Recursive
open Functor.Semantics

-- Natural numbers
NatF : U
NatF = K [1] + Id

Nat : Set
Nat = μ NatF

zero : Nat
zero = inn (inl <>)

suc : Nat -> Nat
suc n = inn (inr n)

plus : Nat -> Nat -> Nat
plus n m = fold NatF φ n where
  φ : ⟦ NatF ⟧ Nat -> Nat
  φ (inl <>) = m
  φ (inr z)  = suc z

-- Lists
ListF : (A : Set) -> U
ListF A = K [1] + K A × Id

List' : (A : Set) -> Set
List' A = μ (ListF A)

nil : {A : Set} -> List' A
nil = inn (inl <>)

cons : {A : Set} -> A -> List' A -> List' A
cons x xs = inn (inr < x , xs >)

sum : List' Nat -> Nat
sum = fold (ListF Nat) φ where
  φ : ⟦ ListF Nat ⟧ Nat -> Nat
  φ (inl <>) = zero
  φ (inr < n , m >) = plus n m

TreeF : U
TreeF = K [1] + Id × Id

Tree : Set
Tree = μ TreeF

leaf : Tree
leaf = inn (inl <>)

node : Tree -> Tree -> Tree
node l r = inn (inr < l , r >)

