------------------------------------------------------------------------
-- Properties of functions, such as associativity and commutativity
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Algebra.FunctionProperties. They are placed here because
-- Algebra.FunctionProperties is a parameterised module, and the
-- parameters are irrelevant for these definitions.

module Algebra.FunctionProperties.Core where

------------------------------------------------------------------------
-- Unary and binary operations

Op₁ : Set → Set
Op₁ A = A → A

Op₂ : Set → Set
Op₂ A = A → A → A
