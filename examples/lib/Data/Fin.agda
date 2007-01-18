
module Data.Fin where

import Data.Nat
import Data.Bool
import Logic.Base
import Logic.Identity

open Data.Nat hiding (_==_ _<_)
open Data.Bool
open Logic.Base

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

module Id where

  _==_ : {n : Nat} -> Fin n -> Fin n -> Bool
  _==_ {zero}  ()	    ()
  _==_ {suc n} fzero	    fzero     = true
  _==_ {suc n} (fsuc i) (fsuc j) = i == j
  _==_ {suc n} fzero	    (fsuc j) = false
  _==_ {suc n} (fsuc i) fzero     = false

  refl : {n : Nat}(i : Fin n) -> IsTrue (i == i)
  refl {zero}  ()
  refl {suc n} fzero	    = tt
  refl {suc n} (fsuc i) = refl i

  subst : {n : Nat}{i j : Fin n} -> (P : Fin n -> Set) -> IsTrue (i == j) -> P i -> P j
  subst {zero}  {}	   {}	P _  _
  subst {suc n} {fzero}	   {fzero}	P eq pi = pi
  subst {suc n} {fsuc i} {fsuc j} P eq pi = subst (\z -> P (fsuc z)) eq pi
  subst {suc n} {fzero}	   {fsuc j}	P () _
  subst {suc n} {fsuc i} {fzero}	P () _

  open Logic.Identity

  FinId : {n : Nat} -> Identity (Fin n)
  FinId = identity (\x y -> IsTrue (x == y))
		   refl
		   (\P i j eq px -> subst P eq px)

_<_ : {n : Nat} -> Fin n -> Fin n -> Bool
_<_ {zero}  ()	 ()
_<_ {suc n} _		 fzero     = false
_<_ {suc n} fzero	 (fsuc j) = true
_<_ {suc n} (fsuc i) (fsuc j) = i < j

fromNat : (n : Nat) -> Fin (suc n)
fromNat  zero	= fzero
fromNat (suc n) = fsuc (fromNat n)

liftSuc : {n : Nat} -> Fin n -> Fin (suc n)
liftSuc {zero}  ()
liftSuc {suc n} fzero	 = fzero
liftSuc {suc n} (fsuc i) = fsuc (liftSuc i)

lift+ : {n : Nat}(m : Nat) -> Fin n -> Fin (m + n)
lift+  zero   i = i
lift+ (suc m) i = liftSuc (lift+ m i)

thin : {n : Nat} -> Fin (suc n) -> Fin n -> Fin (suc n)
thin {zero}  _ ()
thin {suc _} fzero i	       = fsuc i
thin {suc _} (fsuc j) fzero    = fzero
thin {suc _} (fsuc j) (fsuc i) = fsuc (thin j i)

