------------------------------------------------------------------------
-- Vectors
------------------------------------------------------------------------

module Prelude.Vec where

infixr 5 _∷_ _++_

open import Prelude.Nat
open import Prelude.Fin

------------------------------------------------------------------------
-- The type

data Vec (a : Set) : ℕ -> Set where
  []  : Vec a zero
  _∷_ : forall {n} -> a -> Vec a n -> Vec a (suc n)

------------------------------------------------------------------------
-- Some operations

_++_ : forall {a m n} -> Vec a m -> Vec a n -> Vec a (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : forall {a b n} -> (a -> b) -> Vec a n -> Vec b n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

replicate : forall {a n} -> a -> Vec a n
replicate {n = zero}  x = []
replicate {n = suc n} x = x ∷ replicate x

foldr :  forall {a b : Set} {m}
      -> (a -> b -> b) -> b -> Vec a m -> b
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

lookup : forall {a n} -> Fin n -> Vec a n -> a
lookup fz     (x ∷ xs) = x
lookup (fs i) (x ∷ xs) = lookup i xs
