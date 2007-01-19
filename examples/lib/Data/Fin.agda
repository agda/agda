
module Data.Fin where

import Data.Nat
import Data.Bool
import Logic.Base
import Logic.Identity

open Data.Nat hiding (_==_ _<_ _≡_)
open Data.Bool
open Logic.Base

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

{-
module Id where

  _==_ : {n : Nat} -> Fin n -> Fin n -> Bool
  fzero  == fzero  = true
  fsuc i == fsuc j = i == j
  fzero  == fsuc j = false
  fsuc i == fzero  = false

  refl : {n : Nat}(i : Fin n) -> IsTrue (i == i)
  refl  fzero	= tt
  refl (fsuc i) = refl i

  subst : {n : Nat}{i j : Fin n} -> (P : Fin n -> Set) -> IsTrue (i == j) -> P i -> P j
  subst {i = fzero}  {fzero}  P eq pi = pi
  subst {i = fsuc i} {fsuc j} P eq pi = subst (\z -> P (fsuc z)) eq pi
  subst {i = fzero}  {fsuc j} P () _
  subst {i = fsuc i} {fzero}  P () _

  open Logic.Identity

  FinId : {n : Nat} -> Identity (Fin n)
  FinId = identity (\x y -> IsTrue (x == y))
		   refl
		   (\P i j eq px -> subst P eq px)
-}

{-
_<_ : {n : Nat} -> Fin n -> Fin n -> Bool
_      < fzero  = false
fzero  < fsuc j = true
fsuc i < fsuc j = i < j

fromNat : (n : Nat) -> Fin (suc n)
fromNat  zero	= fzero
fromNat (suc n) = fsuc (fromNat n)

liftSuc : {n : Nat} -> Fin n -> Fin (suc n)
liftSuc  fzero	 = fzero
liftSuc (fsuc i) = fsuc (liftSuc i)

lift+ : {n : Nat}(m : Nat) -> Fin n -> Fin (m + n)
lift+  zero   i = i
lift+ (suc m) i = liftSuc (lift+ m i)
-}

thin : {n : Nat} -> Fin (suc n) -> Fin n -> Fin (suc n)
thin  fzero i	       = fsuc i
thin (fsuc j) fzero    = fzero
thin (fsuc j) (fsuc i) = fsuc (thin j i)

-- Two elements of Fin n are either the same or one is the thinning of
-- something with respect to the other.
data ThinView : {n : Nat}(i j : Fin n) -> Set where
  same : {n : Nat}{i : Fin n}		       -> ThinView i i
  diff : {n : Nat}{i : Fin (suc n)}(j : Fin n) -> ThinView i (thin i j)

thinView : {n : Nat}(i j : Fin n) -> ThinView i j
thinView fzero fzero		      = same
thinView  fzero (fsuc j) = diff j
-- thinView {suc zero} (fsuc ()) fzero
thinView {suc (suc n)} (fsuc i) fzero	 = diff fzero
thinView (fsuc i) (fsuc j) = aux i j (thinView i j)
  where
    aux : {n : Nat}(i j : Fin n) -> ThinView i j -> ThinView (fsuc i) (fsuc j)
    aux i .i	       same    = same
    aux i .(thin i j) (diff j) = diff (fsuc j)

