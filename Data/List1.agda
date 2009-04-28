------------------------------------------------------------------------
-- Lists parameterised on things in Set₁
------------------------------------------------------------------------

-- I want universe polymorphism.

module Data.List1 where

open import Data.List as List using (List; []; _∷_)
open import Data.Nat

infixr 5 _∷_ _++_

data List₁ (a : Set₁) : Set₁ where
  []  : List₁ a
  _∷_ : (x : a) (xs : List₁ a) → List₁ a

_++_ : ∀ {a} → List₁ a → List₁ a → List₁ a
[]       ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)

map₀₁ : ∀ {a b} → (a → b) → List a → List₁ b
map₀₁ f []       = []
map₀₁ f (x ∷ xs) = f x ∷ map₀₁ f xs

map₁₁ : ∀ {a b} → (a → b) → List₁ a → List₁ b
map₁₁ f []       = []
map₁₁ f (x ∷ xs) = f x ∷ map₁₁ f xs

replicate : ∀ {a} → (n : ℕ) → a → List₁ a
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

foldr₁₀ : {a : Set₁} {b : Set} → (a → b → b) → b → List₁ a → b
foldr₁₀ c n []       = n
foldr₁₀ c n (x ∷ xs) = c x (foldr₁₀ c n xs)

foldr₁₁ : {a b : Set₁} → (a → b → b) → b → List₁ a → b
foldr₁₁ c n []       = n
foldr₁₁ c n (x ∷ xs) = c x (foldr₁₁ c n xs)

length : ∀ {A} → List₁ A → ℕ
length []       = zero
length (x ∷ xs) = suc (length xs)
