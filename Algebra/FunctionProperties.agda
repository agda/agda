------------------------------------------------------------------------
-- Properties of functions, such as associativity and commutativity
------------------------------------------------------------------------

-- These properties can (for instance) be used to define algebraic
-- structures.

open import Relation.Binary

-- The properties are specified using the equality in the given
-- setoid.

module Algebra.FunctionProperties (s : Setoid) where

open import Data.Product
open Setoid s

------------------------------------------------------------------------
-- Unary and binary operations

Op₁ : Set
Op₁ = carrier -> carrier

Op₂ : Set
Op₂ = carrier -> carrier -> carrier

------------------------------------------------------------------------
-- Properties of operations

Associative : Op₂ -> Set
Associative _•_ = forall x y z -> ((x • y) • z) ≈ (x • (y • z))

Commutative : Op₂ -> Set
Commutative _•_ = forall x y -> (x • y) ≈ (y • x)

LeftIdentity : carrier -> Op₂ -> Set
LeftIdentity e _•_ = forall x -> (e • x) ≈ x

RightIdentity : carrier -> Op₂ -> Set
RightIdentity e _•_ = forall x -> (x • e) ≈ x

Identity : carrier -> Op₂ -> Set
Identity e • = LeftIdentity e • × RightIdentity e •

LeftZero : carrier -> Op₂ -> Set
LeftZero z _•_ = forall x -> (z • x) ≈ z

RightZero : carrier -> Op₂ -> Set
RightZero z _•_ = forall x -> (x • z) ≈ z

Zero : carrier -> Op₂ -> Set
Zero z • = LeftZero z • × RightZero z •

LeftInverse : carrier -> Op₁ -> Op₂ -> Set
LeftInverse e _⁻¹ _•_ = forall x -> (x ⁻¹ • x) ≈ e

RightInverse : carrier -> Op₁ -> Op₂ -> Set
RightInverse e _⁻¹ _•_ = forall x -> (x • (x ⁻¹)) ≈ e

Inverse : carrier -> Op₁ -> Op₂ -> Set
Inverse e ⁻¹ • = LeftInverse e ⁻¹ • × RightInverse e ⁻¹ •

_DistributesOverˡ_ : Op₂ -> Op₂ -> Set
_*_ DistributesOverˡ _+_ =
  forall x y z -> (x * (y + z)) ≈ ((x * y) + (x * z))

_DistributesOverʳ_ : Op₂ -> Op₂ -> Set
_*_ DistributesOverʳ _+_ =
  forall x y z -> ((y + z) * x) ≈ ((y * x) + (z * x))

_DistributesOver_ : Op₂ -> Op₂ -> Set
* DistributesOver + = (* DistributesOverˡ +) × (* DistributesOverʳ +)

_IdempotentOn_ : Op₂ -> carrier -> Set
_•_ IdempotentOn x = (x • x) ≈ x

Idempotent : Op₂ -> Set
Idempotent • = forall x -> • IdempotentOn x

IdempotentFun : Op₁ -> Set
IdempotentFun f = forall x -> f (f x) ≈ f x

_Absorbs_ : Op₂ -> Op₂ -> Set
_•_ Absorbs _∘_ = forall x y -> (x • (x ∘ y)) ≈ x

Absorptive : Op₂ -> Op₂ -> Set
Absorptive • ∘ = (• Absorbs ∘) × (∘ Absorbs •)

Involutive : Op₁ -> Set
Involutive f = forall x -> f (f x) ≈ x
