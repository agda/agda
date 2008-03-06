------------------------------------------------------------------------
-- Lists parameterised on things in Set1
------------------------------------------------------------------------

-- I want universe polymorphism.

module Data.List1 where

open import Data.List
open import Data.Nat

infixr 5 _∷₁_ _++₁_

data [_]₁ (a : Set1) : Set1 where
  []₁  : [ a ]₁
  _∷₁_ : a -> [ a ]₁ -> [ a ]₁

_++₁_ : forall {a} -> [ a ]₁ -> [ a ]₁ -> [ a ]₁
[]₁       ++₁ bs = bs
(a ∷₁ as) ++₁ bs = a ∷₁ (as ++₁ bs)

map₀₁ : forall {a b} -> (a -> b) -> [ a ] -> [ b ]₁
map₀₁ f []       = []₁
map₀₁ f (x ∷ xs) = f x ∷₁ map₀₁ f xs

map₁₁ : forall {a b} -> (a -> b) -> [ a ]₁ -> [ b ]₁
map₁₁ f []₁       = []₁
map₁₁ f (x ∷₁ xs) = f x ∷₁ map₁₁ f xs

replicate₁ : forall {a} -> (n : ℕ) -> a -> [ a ]₁
replicate₁ zero    x = []₁
replicate₁ (suc n) x = x ∷₁ replicate₁ n x

foldr₁₁ : {a b : Set1} -> (a -> b -> b) -> b -> [ a ]₁ -> b
foldr₁₁ c n []₁       = n
foldr₁₁ c n (x ∷₁ xs) = c x (foldr₁₁ c n xs)
