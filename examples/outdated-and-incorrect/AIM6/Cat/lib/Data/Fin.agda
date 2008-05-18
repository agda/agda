
module Data.Fin where

open import Data.Nat hiding (_==_; _<_)
open import Data.Bool
open import Logic.Identity
open import Logic.Base

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

pred : {n : Nat} -> Fin (suc (suc n)) -> Fin (suc n)
pred fzero    = fzero
pred (fsuc i) = i

fzero≠fsuc : {n : Nat}{i : Fin n} -> fzero ≢ fsuc i
fzero≠fsuc ()

fsuc-inj : {n : Nat}{i j : Fin n} -> fsuc i ≡ fsuc j -> i ≡ j
fsuc-inj refl = refl

_==_ : {n : Nat}(i j : Fin n) -> i ≡ j \/ i ≢ j
fzero  == fzero  = \/-IL refl
fzero  == fsuc j = \/-IR fzero≠fsuc
fsuc i == fzero  = \/-IR (sym≢ fzero≠fsuc)
fsuc i == fsuc j = aux i j (i == j)
  where
    aux : {n : Nat}(i j : Fin n) -> i ≡ j \/ i ≢ j -> fsuc i ≡ fsuc j \/ fsuc i ≢ fsuc j
    aux i .i (\/-IL refl) = \/-IL refl
    aux i j  (\/-IR i≠j)  = \/-IR \si=sj -> i≠j (fsuc-inj si=sj)

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
thinView {suc zero} (fsuc ()) fzero
thinView {suc (suc n)} (fsuc i) fzero	 = diff fzero
thinView (fsuc i) (fsuc j) = aux i j (thinView i j)
  where
    aux : {n : Nat}(i j : Fin n) -> ThinView i j -> ThinView (fsuc i) (fsuc j)
    aux i .i	       same    = same
    aux i .(thin i j) (diff j) = diff (fsuc j)

thin-ij≠i : {n : Nat}(i : Fin (suc n))(j : Fin n) -> thin i j ≢ i
thin-ij≠i  fzero    j	    ()
thin-ij≠i (fsuc i)  fzero   ()
thin-ij≠i (fsuc i) (fsuc j) eq = thin-ij≠i i j (fsuc-inj eq)

-- Thickening.
--    thin i (thick i j) ≡ j  ?
--    thick i (thin i j) ≡ j
thick : {n : Nat}(i j : Fin (suc n)) -> i ≢ j -> Fin n
thick i j i≠j = thick' i j i≠j (thinView i j) where
  thick' : {n : Nat}(i j : Fin (suc n)) -> i ≢ j -> ThinView i j -> Fin n
  thick' i .i	       i≠i same	   = elim-False (i≠i refl)
  thick' i .(thin i j) _  (diff j) = j

-- thin∘thick=id : {n : Nat}(i j : Fin (suc n))(p : i ≢ j) ->
-- 		thin i (thick i j p) ≡ j
-- thin∘thick=id i j p = ?
-- 
-- thick∘thin=id : {n : Nat}(i : Fin (suc n))(j : Fin n) ->
-- 		thick i (thin i j) (sym≢ (thin-ij≠i i j)) ≡ j
-- thick∘thin=id i j = ?
-- 
