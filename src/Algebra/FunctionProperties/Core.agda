------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of functions, such as associativity and commutativity
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Algebra.FunctionProperties. They are placed here because
-- Algebra.FunctionProperties is a parameterised module, and some of
-- the parameters are irrelevant for these definitions.

module Algebra.FunctionProperties.Core where

open import Level

------------------------------------------------------------------------
-- Unary and binary operations

Op₁ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₁ A = A → A

Op₂ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₂ A = A → A → A
