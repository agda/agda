------------------------------------------------------------------------
-- Lists parameterised on things in Set1
------------------------------------------------------------------------

-- I want universe polymorphism.

module Data.List1 where

import Data.List as List
open List using ([_]; []; _∷_)
open import Data.Nat

infixr 5 _∷_ _++_

data [_]₁ (a : Set1) : Set1 where
  []  : [ a ]₁
  _∷_ : (x : a) (xs : [ a ]₁) -> [ a ]₁

_++_ : forall {a} -> [ a ]₁ -> [ a ]₁ -> [ a ]₁
[]       ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)

map₀₁ : forall {a b} -> (a -> b) -> [ a ] -> [ b ]₁
map₀₁ f []       = []
map₀₁ f (x ∷ xs) = f x ∷ map₀₁ f xs

map₁₁ : forall {a b} -> (a -> b) -> [ a ]₁ -> [ b ]₁
map₁₁ f []       = []
map₁₁ f (x ∷ xs) = f x ∷ map₁₁ f xs

replicate : forall {a} -> (n : ℕ) -> a -> [ a ]₁
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

foldr₁₀ : {a : Set1} {b : Set} -> (a -> b -> b) -> b -> [ a ]₁ -> b
foldr₁₀ c n []       = n
foldr₁₀ c n (x ∷ xs) = c x (foldr₁₀ c n xs)

foldr₁₁ : {a b : Set1} -> (a -> b -> b) -> b -> [ a ]₁ -> b
foldr₁₁ c n []       = n
foldr₁₁ c n (x ∷ xs) = c x (foldr₁₁ c n xs)

length : forall {A} -> [ A ]₁ -> ℕ
length []       = zero
length (x ∷ xs) = suc (length xs)
