
module Problem3 where

open import Problem1
open import Problem2

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data False : Set where

-- 3.1

empty : Fin zero -> False
empty ()

-- 3.2

_!_ : {A : Set}{n : Nat} -> Vec A n -> Fin n -> A
ε        ! ()
(x ► xs) ! fzero  = x
(x ► xs) ! fsuc i = xs ! i

-- 3.3

-- The simply typed composition would do here, but the more
-- dependent version is more interesting.
-- _∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C

_∘_ : {A B : Set}{C : B -> Set}(f : (x : B) -> C x)
      (g : A -> B)(x : A) -> C (g x)
(f ∘ g) x = f (g x)

tabulate : {A : Set}{n : Nat} -> (Fin n -> A) -> Vec A n
tabulate {n = zero } f = ε
tabulate {n = suc n} f = f fzero ► tabulate (f ∘ fsuc)
