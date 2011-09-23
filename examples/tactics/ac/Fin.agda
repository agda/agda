
module Fin where

import Nat
import Bool

open Nat hiding (_==_; _<_)
open Bool

data FZero : Set where

data FSuc (A : Set) : Set where
  fz : FSuc A
  fs : A -> FSuc A

data Fin (n : Nat) : Set

Fin' : Nat -> Set
Fin' zero    = FZero
Fin' (suc n) = FSuc (Fin n)

data Fin n where
  fin : Fin' n -> Fin n

fzero : {n : Nat} -> Fin (suc n)
fzero = fin fz

fsuc : {n : Nat} -> Fin n -> Fin (suc n)
fsuc n = fin (fs n)

_==_ : {n : Nat} -> Fin n -> Fin n -> Bool
_==_ {zero}  (fin ())     (fin ())
_==_ {suc n} (fin fz)     (fin fz)     = true
_==_ {suc n} (fin (fs i)) (fin (fs j)) = i == j
_==_ {suc n} (fin fz)     (fin (fs j)) = false
_==_ {suc n} (fin (fs i)) (fin fz)     = false

subst : {n : Nat}{i j : Fin n} -> (P : Fin n -> Set) -> IsTrue (i == j) -> P i -> P j
subst {zero}  {fin ()}     {fin ()}     P _  _
subst {suc n} {fin fz}     {fin fz}     P eq pi = pi
subst {suc n} {fin (fs i)} {fin (fs j)} P eq pi = subst (\z -> P (fsuc z)) eq pi
subst {suc n} {fin fz}     {fin (fs j)} P () _
subst {suc n} {fin (fs i)} {fin fz}     P () _

_<_ : {n : Nat} -> Fin n -> Fin n -> Bool
_<_ {zero}  (fin ())     (fin ())
_<_ {suc n} _            (fin fz)     = false
_<_ {suc n} (fin fz)     (fin (fs j)) = true
_<_ {suc n} (fin (fs i)) (fin (fs j)) = i < j

fromNat : (n : Nat) -> Fin (suc n)
fromNat  zero   = fzero
fromNat (suc n) = fsuc (fromNat n)

liftSuc : {n : Nat} -> Fin n -> Fin (suc n)
liftSuc {zero}  (fin ())
liftSuc {suc n} (fin fz)     = fin fz
liftSuc {suc n} (fin (fs i)) = fsuc (liftSuc i)

lift+ : {n : Nat}(m : Nat) -> Fin n -> Fin (m + n)
lift+  zero   i = i
lift+ (suc m) i = liftSuc (lift+ m i)

