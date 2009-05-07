------------------------------------------------------------------------
-- Properties of functions, such as associativity and commutativity
------------------------------------------------------------------------

-- These properties can (for instance) be used to define algebraic
-- structures.

open import Relation.Binary

-- The properties are specified using the following relation as
-- "equality".

module Algebra.FunctionProperties {A} (_≈_ : Rel A) where

open import Data.Product

------------------------------------------------------------------------
-- Unary and binary operations

open import Algebra.FunctionProperties.Core public

------------------------------------------------------------------------
-- Properties of operations

Associative : Op₂ A → Set
Associative _∙_ = ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))

Commutative : Op₂ A → Set
Commutative _∙_ = ∀ x y → (x ∙ y) ≈ (y ∙ x)

LeftIdentity : A → Op₂ A → Set
LeftIdentity e _∙_ = ∀ x → (e ∙ x) ≈ x

RightIdentity : A → Op₂ A → Set
RightIdentity e _∙_ = ∀ x → (x ∙ e) ≈ x

Identity : A → Op₂ A → Set
Identity e ∙ = LeftIdentity e ∙ × RightIdentity e ∙

LeftZero : A → Op₂ A → Set
LeftZero z _∙_ = ∀ x → (z ∙ x) ≈ z

RightZero : A → Op₂ A → Set
RightZero z _∙_ = ∀ x → (x ∙ z) ≈ z

Zero : A → Op₂ A → Set
Zero z ∙ = LeftZero z ∙ × RightZero z ∙

LeftInverse : A → Op₁ A → Op₂ A → Set
LeftInverse e _⁻¹ _∙_ = ∀ x → (x ⁻¹ ∙ x) ≈ e

RightInverse : A → Op₁ A → Op₂ A → Set
RightInverse e _⁻¹ _∙_ = ∀ x → (x ∙ (x ⁻¹)) ≈ e

Inverse : A → Op₁ A → Op₂ A → Set
Inverse e ⁻¹ ∙ = LeftInverse e ⁻¹ ∙ × RightInverse e ⁻¹ ∙

_DistributesOverˡ_ : Op₂ A → Op₂ A → Set
_*_ DistributesOverˡ _+_ =
  ∀ x y z → (x * (y + z)) ≈ ((x * y) + (x * z))

_DistributesOverʳ_ : Op₂ A → Op₂ A → Set
_*_ DistributesOverʳ _+_ =
  ∀ x y z → ((y + z) * x) ≈ ((y * x) + (z * x))

_DistributesOver_ : Op₂ A → Op₂ A → Set
* DistributesOver + = (* DistributesOverˡ +) × (* DistributesOverʳ +)

_IdempotentOn_ : Op₂ A → A → Set
_∙_ IdempotentOn x = (x ∙ x) ≈ x

Idempotent : Op₂ A → Set
Idempotent ∙ = ∀ x → ∙ IdempotentOn x

IdempotentFun : Op₁ A → Set
IdempotentFun f = ∀ x → f (f x) ≈ f x

_Absorbs_ : Op₂ A → Op₂ A → Set
_∙_ Absorbs _∘_ = ∀ x y → (x ∙ (x ∘ y)) ≈ x

Absorptive : Op₂ A → Op₂ A → Set
Absorptive ∙ ∘ = (∙ Absorbs ∘) × (∘ Absorbs ∙)

Involutive : Op₁ A → Set
Involutive f = ∀ x → f (f x) ≈ x
