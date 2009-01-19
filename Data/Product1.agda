------------------------------------------------------------------------
-- Products (variants for Set1)
------------------------------------------------------------------------

-- I want universe polymorphism.

module Data.Product1 where

open import Data.Function
open import Relation.Nullary

infixr 4 _,_

------------------------------------------------------------------------
-- Definition

data Σ₀₁ (a : Set) (b : a → Set1) : Set1 where
  _,_ : (x : a) (y : b x) → Σ₀₁ a b

data Σ₁₀ (a : Set1) (b : a → Set) : Set1 where
  _,_ : (x : a) (y : b x) → Σ₁₀ a b

data Σ₁₁ (a : Set1) (b : a → Set1) : Set1 where
  _,_ : (x : a) (y : b x) → Σ₁₁ a b

------------------------------------------------------------------------
-- Functions

proj₀₁₁ : ∀ {a b} → Σ₀₁ a b → a
proj₀₁₁ (x , y) = x

proj₀₁₂ : ∀ {a b} → (p : Σ₀₁ a b) → b (proj₀₁₁ p)
proj₀₁₂ (x , y) = y

proj₁₀₁ : ∀ {a b} → Σ₁₀ a b → a
proj₁₀₁ (x , y) = x

proj₁₀₂ : ∀ {a b} → (p : Σ₁₀ a b) → b (proj₁₀₁ p)
proj₁₀₂ (x , y) = y

proj₁₁₁ : ∀ {a b} → Σ₁₁ a b → a
proj₁₁₁ (x , y) = x

proj₁₁₂ : ∀ {a b} → (p : Σ₁₁ a b) → b (proj₁₁₁ p)
proj₁₁₂ (x , y) = y
