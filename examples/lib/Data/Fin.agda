
module Data.Fin where

import Data.Nat
import Data.Bool
import Logic.Base
import Logic.Identity

open Data.Nat, hiding (_==_, _<_)
open Data.Bool
open Logic.Base

data FZero : Set where

data FSuc (A:Set) : Set where
  fz : FSuc A
  fs : A -> FSuc A

mutual

  Fin' : Nat -> Set
  Fin' zero    = FZero
  Fin' (suc n) = FSuc (Fin n)

  data Fin (n:Nat) : Set where
    fin : Fin' n -> Fin n

fzero : {n : Nat} -> Fin (suc n)
fzero = fin fz

fsuc : {n : Nat} -> Fin n -> Fin (suc n)
fsuc n = fin (fs n)

module Id where

  _==_ : {n : Nat} -> Fin n -> Fin n -> Bool
  _==_ {zero}  (fin ())	    (fin ())
  _==_ {suc n} (fin fz)	    (fin fz)     = true
  _==_ {suc n} (fin (fs i)) (fin (fs j)) = i == j
  _==_ {suc n} (fin fz)	    (fin (fs j)) = false
  _==_ {suc n} (fin (fs i)) (fin fz)     = false

  refl : {n : Nat}(i : Fin n) -> IsTrue (i == i)
  refl {zero}  (fin ())
  refl {suc n} (fin fz)	    = tt
  refl {suc n} (fin (fs i)) = refl i

  subst : {n : Nat}{i, j : Fin n} -> (P : Fin n -> Set) -> IsTrue (i == j) -> P i -> P j
  subst {zero}  {fin ()}	   {fin ()}	P _  _
  subst {suc n} {fin fz}	   {fin fz}	P eq pi = pi
  subst {suc n} {fin (fs i)} {fin (fs j)} P eq pi = subst (\z -> P (fsuc z)) eq pi
  subst {suc n} {fin fz}	   {fin (fs j)}	P () _
  subst {suc n} {fin (fs i)} {fin fz}	P () _

  open Logic.Identity

  FinId : {n : Nat} -> Identity (Fin n)
  FinId = identity (\x y -> IsTrue (x == y))
		   refl
		   (\P i j eq px -> subst P eq px)

_<_ : {n : Nat} -> Fin n -> Fin n -> Bool
_<_ {zero}  (fin ())	 (fin ())
_<_ {suc n} _		 (fin fz)     = false
_<_ {suc n} (fin fz)	 (fin (fs j)) = true
_<_ {suc n} (fin (fs i)) (fin (fs j)) = i < j

fromNat : (n : Nat) -> Fin (suc n)
fromNat  zero	= fzero
fromNat (suc n) = fsuc (fromNat n)

liftSuc : {n : Nat} -> Fin n -> Fin (suc n)
liftSuc {zero}  (fin ())
liftSuc {suc n} (fin fz)     = fin fz
liftSuc {suc n} (fin (fs i)) = fsuc (liftSuc i)

lift+ : {n : Nat}(m : Nat) -> Fin n -> Fin (m + n)
lift+  zero   i = i
lift+ (suc m) i = liftSuc (lift+ m i)

thin : {n : Nat} -> Fin (suc n) -> Fin n -> Fin (suc n)
thin {zero}  _ (fin ())
thin {suc _} (fin fz) i		       = fsuc i
thin {suc _} (fin (fs j)) (fin fz)     = fzero
thin {suc _} (fin (fs j)) (fin (fs i)) = fsuc (thin j i)

