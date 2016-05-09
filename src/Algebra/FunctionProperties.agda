------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of functions, such as associativity and commutativity
------------------------------------------------------------------------

-- These properties can (for instance) be used to define algebraic
-- structures.

open import Level
open import Relation.Binary
open import Data.Sum

-- The properties are specified using the following relation as
-- "equality".

module Algebra.FunctionProperties
         {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Data.Product

------------------------------------------------------------------------
-- Unary and binary operations

open import Algebra.FunctionProperties.Core public

------------------------------------------------------------------------
-- Properties of operations

Associative : Op₂ A → Set _
Associative _∙_ = ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))

Commutative : Op₂ A → Set _
Commutative _∙_ = ∀ x y → (x ∙ y) ≈ (y ∙ x)

LeftIdentity : A → Op₂ A → Set _
LeftIdentity e _∙_ = ∀ x → (e ∙ x) ≈ x

RightIdentity : A → Op₂ A → Set _
RightIdentity e _∙_ = ∀ x → (x ∙ e) ≈ x

Identity : A → Op₂ A → Set _
Identity e ∙ = LeftIdentity e ∙ × RightIdentity e ∙

LeftZero : A → Op₂ A → Set _
LeftZero z _∙_ = ∀ x → (z ∙ x) ≈ z

RightZero : A → Op₂ A → Set _
RightZero z _∙_ = ∀ x → (x ∙ z) ≈ z

Zero : A → Op₂ A → Set _
Zero z ∙ = LeftZero z ∙ × RightZero z ∙

LeftInverse : A → Op₁ A → Op₂ A → Set _
LeftInverse e _⁻¹ _∙_ = ∀ x → ((x ⁻¹) ∙ x) ≈ e

RightInverse : A → Op₁ A → Op₂ A → Set _
RightInverse e _⁻¹ _∙_ = ∀ x → (x ∙ (x ⁻¹)) ≈ e

Inverse : A → Op₁ A → Op₂ A → Set _
Inverse e ⁻¹ ∙ = LeftInverse e ⁻¹ ∙ × RightInverse e ⁻¹ ∙

_DistributesOverˡ_ : Op₂ A → Op₂ A → Set _
_*_ DistributesOverˡ _+_ =
  ∀ x y z → (x * (y + z)) ≈ ((x * y) + (x * z))

_DistributesOverʳ_ : Op₂ A → Op₂ A → Set _
_*_ DistributesOverʳ _+_ =
  ∀ x y z → ((y + z) * x) ≈ ((y * x) + (z * x))

_DistributesOver_ : Op₂ A → Op₂ A → Set _
* DistributesOver + = (* DistributesOverˡ +) × (* DistributesOverʳ +)

_IdempotentOn_ : Op₂ A → A → Set _
_∙_ IdempotentOn x = (x ∙ x) ≈ x

Idempotent : Op₂ A → Set _
Idempotent ∙ = ∀ x → ∙ IdempotentOn x

IdempotentFun : Op₁ A → Set _
IdempotentFun f = ∀ x → f (f x) ≈ f x

Selective : Op₂ A → Set _
Selective _∙_ = ∀ x y → (x ∙ y) ≈ x ⊎ (x ∙ y) ≈ y

_Absorbs_ : Op₂ A → Op₂ A → Set _
_∙_ Absorbs _∘_ = ∀ x y → (x ∙ (x ∘ y)) ≈ x

Absorptive : Op₂ A → Op₂ A → Set _
Absorptive ∙ ∘ = (∙ Absorbs ∘) × (∘ Absorbs ∙)

Involutive : Op₁ A → Set _
Involutive f = ∀ x → f (f x) ≈ x
