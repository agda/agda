
module Data.Vec where

open import Prelude
open import Data.Nat
open import Data.Fin hiding (_==_; _<_)
open import Logic.Structure.Applicative
open import Logic.Identity
open import Logic.Base

infixl 90 _#_
infixr 50 _::_
infixl 45 _!_ _[!]_

data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

-- Indexing
_!_ : {n : Nat}{A : Set} -> Vec A n -> Fin n -> A
[]      ! ()
x :: xs ! fzero  = x
x :: xs ! fsuc i = xs ! i

-- Insertion
insert : {n : Nat}{A : Set} -> Fin (suc n) -> A -> Vec A n -> Vec A (suc n)
insert fzero     y  xs       = y :: xs
insert (fsuc i)  y (x :: xs) = x :: insert i y xs
insert (fsuc ()) y []

-- Index view
data IndexView {A : Set} : {n : Nat}(i : Fin n) -> Vec A n -> Set where
   ixV : {n : Nat}{i : Fin (suc n)}(x : A)(xs : Vec A n) ->
         IndexView i (insert i x xs)

_[!]_ : {A : Set}{n : Nat}(xs : Vec A n)(i : Fin n) -> IndexView i xs
[]      [!] ()
x :: xs [!] fzero  = ixV x xs
x :: xs [!] fsuc i = aux xs i (xs [!] i)
  where
    aux : {n : Nat}(xs : Vec _ n)(i : Fin n) ->
          IndexView i xs -> IndexView (fsuc i) (x :: xs)
    aux .(insert i y xs) i (ixV y xs) = ixV y (x :: xs)

-- Build a vector from an indexing function (inverse of _!_)
build : {n : Nat}{A : Set} -> (Fin n -> A) -> Vec A n
build {zero } f = []
build {suc _} f = f fzero :: build (f ∘ fsuc)

-- Constant vectors
vec : {n : Nat}{A : Set} -> A -> Vec A n
vec {zero } _ = []
vec {suc m} x = x :: vec x

-- Vector application
_#_ : {n : Nat}{A B : Set} -> Vec (A -> B) n -> Vec A n -> Vec B n
[]        # []        = []
(f :: fs) # (x :: xs) = f x :: fs # xs

-- Vectors of length n form an applicative structure
ApplicativeVec : {n : Nat} -> Applicative (\A -> Vec A n)
ApplicativeVec {n} = applicative (vec {n}) (_#_ {n})

-- Map
map : {n : Nat}{A B : Set} -> (A -> B) -> Vec A n -> Vec B n
map f xs = vec f # xs

-- Zip
zip : {n : Nat}{A B C : Set} -> (A -> B -> C) -> Vec A n -> Vec B n -> Vec C n
zip f xs ys = vec f # xs # ys

module Elem where

  infix 40 _∈_ _∉_

  data _∈_ {A : Set}(x : A) : {n : Nat}(xs : Vec A n) -> Set where
    hd : {n : Nat}       {xs : Vec A n}           -> x ∈ x :: xs
    tl : {n : Nat}{y : A}{xs : Vec A n} -> x ∈ xs -> x ∈ y :: xs

  data _∉_ {A : Set}(x : A) : {n : Nat}(xs : Vec A n) -> Set where
    nl  : x ∉ []
    cns : {n : Nat}{y : A}{xs : Vec A n} -> x ≢ y -> x ∉ xs -> x ∉ y :: xs

  ∉=¬∈ : {A : Set}{x : A}{n : Nat}{xs : Vec A n} -> x ∉ xs -> ¬ (x ∈ xs)
  ∉=¬∈ nl         ()
  ∉=¬∈ {A} (cns x≠x _) hd    = elim-False (x≠x refl)
  ∉=¬∈ {A} (cns _ ne) (tl e) = ∉=¬∈ ne e

  ∈=¬∉ : {A : Set}{x : A}{n : Nat}{xs : Vec A n} -> x ∈ xs -> ¬ (x ∉ xs)
  ∈=¬∉ e ne = ∉=¬∈ ne e

  find : {A : Set}{n : Nat} -> ((x y : A) -> (x ≡ y) \/ (x ≢ y)) ->
         (x : A)(xs : Vec A n) -> x ∈ xs \/ x ∉ xs
  find _  _ []        = \/-IR nl
  find eq y (x :: xs) = aux x y (eq y x) (find eq y xs) where
    aux : forall x y -> (y ≡ x) \/ (y ≢ x) -> y ∈ xs \/ y ∉ xs -> y ∈ x :: xs \/ y ∉ x :: xs
    aux x .x (\/-IL refl)  _           = \/-IL hd
    aux x y  (\/-IR y≠x)  (\/-IR y∉xs) = \/-IR (cns y≠x y∉xs)
    aux x y  (\/-IR _)    (\/-IL y∈xs) = \/-IL (tl y∈xs)

  delete : {A : Set}{n : Nat}(x : A)(xs : Vec A (suc n)) -> x ∈ xs -> Vec A n
  delete           .x (x :: xs)  hd    = xs
  delete {A}{zero } _  ._       (tl ())
  delete {A}{suc _} y (x :: xs) (tl p) = x :: delete y xs p

