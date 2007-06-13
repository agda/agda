------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

module Prelude.List where

infixr 5 _∷_ _++_

open import Prelude.Nat
open import Prelude.Sum

------------------------------------------------------------------------
-- The type

data [_] (a : Set) : Set where
  []  : [ a ]
  _∷_ : a -> [ a ] -> [ a ]

------------------------------------------------------------------------
-- Some operations

_++_ : forall {a} -> [ a ] -> [ a ] -> [ a ]
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : forall {a b} -> (a -> b) -> [ a ] -> [ b ]
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

replicate : forall {a} -> (n : ℕ) -> a -> [ a ]
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

foldr : {a b : Set} -> (a -> b -> b) -> b -> [ a ] -> b
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

-- Possibly the following functions should be called lefts and rights.

inj₁s : forall {a b} -> [ a ⊎ b ] -> [ a ]
inj₁s []            = []
inj₁s (inj₁ x ∷ xs) = x ∷ inj₁s xs
inj₁s (inj₂ x ∷ xs) = inj₁s xs

inj₂s : forall {a b} -> [ a ⊎ b ] -> [ b ]
inj₂s []            = []
inj₂s (inj₁ x ∷ xs) = inj₂s xs
inj₂s (inj₂ x ∷ xs) = x ∷ inj₂s xs
