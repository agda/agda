------------------------------------------------------------------------
-- Some algebraic structures
------------------------------------------------------------------------

open import Relation.Binary

module Algebra (s : Setoid) where

open import Data.Product
private
  open module S = SetoidOps s

------------------------------------------------------------------------
-- Unary and binary operations

Op₁ : Set
Op₁ = carrier -> carrier

Op₂ : Set
Op₂ = carrier -> carrier -> carrier

------------------------------------------------------------------------
-- Properties of operations

Associative : Op₂ -> Set
Associative _•_ = forall x y z -> (x • (y • z)) ≈ ((x • y) • z)

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

Idempotent₁ : Op₁ -> Set
Idempotent₁ f = forall x -> f (f x) ≈ f x

_Absorbs_ : Op₂ -> Op₂ -> Set
_•_ Absorbs _∘_ = forall x y -> (x • (x ∘ y)) ≈ x

Absorptive : Op₂ -> Op₂ -> Set
Absorptive • ∘ = (• Absorbs ∘) × (∘ Absorbs •)

Involutive : Op₁ -> Set
Involutive f = forall x -> f (f x) ≈ x

------------------------------------------------------------------------
-- Combinations of properties (one binary operation)

-- First some abbreviations:

_Preserves-≈ : Op₁ -> Set
• Preserves-≈ = • Preserves _≈_ → _≈_

_Preserves₂-≈ : Op₂ -> Set
• Preserves₂-≈ = • Preserves₂ _≈_ → _≈_ → _≈_

record Semigroup (• : Op₂) : Set where
  assoc    : Associative •
  •-pres-≈ : • Preserves₂-≈

record Monoid (• : Op₂) (ε : carrier) : Set where
  semigroup : Semigroup •
  identity  : Identity ε •

record CommutativeMonoid (• : Op₂) (ε : carrier) : Set where
  monoid : Monoid • ε
  comm   : Commutative •

record Group (• : Op₂) (ε : carrier) (⁻¹ : Op₁) : Set where
  monoid    : Monoid • ε
  inverse   : Inverse ε ⁻¹ •
  ⁻¹-pres-≈ : ⁻¹ Preserves-≈

record AbelianGroup (• : Op₂) (ε : carrier) (⁻¹ : Op₁) : Set where
  group : Group • ε ⁻¹
  comm  : Commutative •

------------------------------------------------------------------------
-- Combinations of properties (two binary operations)

record Semiring (+ * : Op₂) (0# 1# : carrier) : Set where
  +-monoid : CommutativeMonoid + 0#
  *-monoid : Monoid * 1#
  distrib  : * DistributesOver +
  zero     : Zero 0# *

record CommutativeSemiring (+ * : Op₂) (0# 1# : carrier) : Set where
  semiring : Semiring + * 0# 1#
  *-comm   : Commutative *

record Ring (+ * : Op₂) (- : Op₁) (0# 1# : carrier) : Set where
  +-group  : AbelianGroup + 0# -
  *-monoid : Monoid * 1#
  distrib  : * DistributesOver +

record CommutativeRing (+ * : Op₂) (- : Op₁) (0# 1# : carrier) : Set where
  ring   : Ring + * - 0# 1#
  *-comm : Commutative *

-- A structure which lies somewhere between commutative rings and
-- commutative semirings

record AlmostCommRing (_+_ _*_ : Op₂)
                      (¬_ : Op₁)
                      (0# 1# : carrier) : Set where
  commSemiring : CommutativeSemiring _+_ _*_ 0# 1#
  ¬-pres-≈     : ¬_ Preserves-≈
  ¬-*-distribˡ : forall x y -> ((¬ x) * y) ≈ (¬ (x * y))
  ¬-+-comm     : forall x y -> ((¬ x) + (¬ y)) ≈ (¬ (x + y))

record Lattice (∨ ∧ : Op₂) : Set where
  ∨-comm     : Commutative ∨
  ∨-assoc    : Associative ∨
  ∨-pres-≈   : ∨ Preserves₂-≈
  ∧-comm     : Commutative ∧
  ∧-assoc    : Associative ∧
  ∧-pres-≈   : ∧ Preserves₂-≈
  absorptive : Absorptive ∨ ∧

record DistributiveLattice (∨ ∧ : Op₂) : Set where
  lattice      : Lattice ∨ ∧
  ∨-∧-distribˡ : ∨ DistributesOverˡ ∧

record BooleanAlgebra (∨ ∧ : Op₂) (¬ : Op₁) (⊤ ⊥ : carrier) : Set where
  distLattice   : DistributiveLattice ∨ ∧
  ∨-complementʳ : RightInverse ⊤ ¬ ∨
  ∧-complementʳ : RightInverse ⊥ ¬ ∧
  ¬-pres-≈      : ¬ Preserves-≈
