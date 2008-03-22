------------------------------------------------------------------------
-- Lists parameterised on things in Set1
------------------------------------------------------------------------

-- I want universe polymorphism.

module Data.List1 where

open import Data.List
open import Data.Nat

infixr 5 _∷_ _++₁_

data [_]₁ (a : Set1) : Set1 where
  []  : [ a ]₁
  _∷_ : a -> [ a ]₁ -> [ a ]₁

_++₁_ : forall {a} -> [ a ]₁ -> [ a ]₁ -> [ a ]₁
[]       ++₁ bs = bs
(a ∷ as) ++₁ bs = a ∷ (as ++₁ bs)

map₀₁ : forall {a b} -> (a -> b) -> [ a ] -> [ b ]₁
map₀₁ f []       = []
map₀₁ f (x ∷ xs) = f x ∷ map₀₁ f xs

map₁₁ : forall {a b} -> (a -> b) -> [ a ]₁ -> [ b ]₁
map₁₁ f []       = []
map₁₁ f (x ∷ xs) = f x ∷ map₁₁ f xs

replicate₁ : forall {a} -> (n : ℕ) -> a -> [ a ]₁
replicate₁ zero    x = []
replicate₁ (suc n) x = x ∷ replicate₁ n x

foldr₁₁ : {a b : Set1} -> (a -> b -> b) -> b -> [ a ]₁ -> b
foldr₁₁ c n []       = n
foldr₁₁ c n (x ∷ xs) = c x (foldr₁₁ c n xs)
