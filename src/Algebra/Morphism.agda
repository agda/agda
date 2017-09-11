------------------------------------------------------------------------
-- The Agda standard library
--
-- Morphisms between algebraic structures
------------------------------------------------------------------------

module Algebra.Morphism where

open import Relation.Binary
open import Algebra
open import Algebra.FunctionProperties
import Algebra.Properties.Group as GroupP
open import Function
open import Data.Product
open import Level
import Relation.Binary.EqReasoning as EqR

------------------------------------------------------------------------
-- Basic definitions

module Definitions {f t ℓ}
                   (From : Set f) (To : Set t) (_≈_ : Rel To ℓ) where
  Morphism : Set _
  Morphism = From → To

  Homomorphic₀ : Morphism → From → To → Set _
  Homomorphic₀ ⟦_⟧ ∙ ∘ = ⟦ ∙ ⟧ ≈ ∘

  Homomorphic₁ : Morphism → Fun₁ From → Op₁ To → Set _
  Homomorphic₁ ⟦_⟧ ∙_ ∘_ = ∀ x → ⟦ ∙ x ⟧ ≈ (∘ ⟦ x ⟧)

  Homomorphic₂ : Morphism → Fun₂ From → Op₂ To → Set _
  Homomorphic₂ ⟦_⟧ _∙_ _∘_ =
    ∀ x y → ⟦ x ∙ y ⟧ ≈ (⟦ x ⟧ ∘ ⟦ y ⟧)

------------------------------------------------------------------------
-- Structure homomorphisms

module _ {c₁ ℓ₁ c₂ ℓ₂}
         (From : Semigroup c₁ ℓ₁)
         (To   : Semigroup c₂ ℓ₂) where

  private
    module F = Semigroup From
    module T = Semigroup To
  open Definitions F.Carrier T.Carrier T._≈_

  record IsSemigroupMorphism (⟦_⟧ : Morphism) :
         Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      ⟦⟧-cong : ⟦_⟧ Preserves F._≈_ ⟶ T._≈_
      ∙-homo  : Homomorphic₂ ⟦_⟧ F._∙_ T._∙_

  syntax IsSemigroupMorphism From To F = F Is From -Semigroup⟶ To

module _ {c₁ ℓ₁ c₂ ℓ₂}
         (From : Monoid c₁ ℓ₁)
         (To   : Monoid c₂ ℓ₂) where

  private
    module F = Monoid From
    module T = Monoid To
  open Definitions F.Carrier T.Carrier T._≈_

  record IsMonoidMorphism (⟦_⟧ : Morphism) :
         Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      sm-homo : IsSemigroupMorphism F.semigroup T.semigroup ⟦_⟧
      ε-homo  : Homomorphic₀ ⟦_⟧ F.ε T.ε

    open IsSemigroupMorphism sm-homo public

  syntax IsMonoidMorphism From To F = F Is From -Monoid⟶ To

module _ {c₁ ℓ₁ c₂ ℓ₂}
         (From : CommutativeMonoid c₁ ℓ₁)
         (To   : CommutativeMonoid c₂ ℓ₂) where

  private
    module F = CommutativeMonoid From
    module T = CommutativeMonoid To
  open Definitions F.Carrier T.Carrier T._≈_

  record IsCommutativeMonoidMorphism (⟦_⟧ : Morphism) :
         Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      mn-homo : IsMonoidMorphism F.monoid T.monoid ⟦_⟧

    open IsMonoidMorphism mn-homo public

  syntax IsCommutativeMonoidMorphism From To F = F Is From -CommutativeMonoid⟶ To

module _ {c₁ ℓ₁ c₂ ℓ₂}
         (From : IdempotentCommutativeMonoid c₁ ℓ₁)
         (To   : IdempotentCommutativeMonoid c₂ ℓ₂) where

  private
    module F = IdempotentCommutativeMonoid From
    module T = IdempotentCommutativeMonoid To
  open Definitions F.Carrier T.Carrier T._≈_

  record IsIdempotentCommutativeMonoidMorphism (⟦_⟧ : Morphism) :
         Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      mn-homo : IsMonoidMorphism F.monoid T.monoid ⟦_⟧

    open IsMonoidMorphism mn-homo public

    isCommutativeMonoidMorphism :
      IsCommutativeMonoidMorphism F.commutativeMonoid T.commutativeMonoid ⟦_⟧
    isCommutativeMonoidMorphism = record { mn-homo = mn-homo }

  syntax IsIdempotentCommutativeMonoidMorphism From To F = F Is From -IdempotentCommutativeMonoid⟶ To

module _ {c₁ ℓ₁ c₂ ℓ₂}
         (From : Group c₁ ℓ₁)
         (To   : Group c₂ ℓ₂) where

  private
    module F = Group From
    module T = Group To
  open Definitions F.Carrier T.Carrier T._≈_

  record IsGroupMorphism (⟦_⟧ : Morphism) :
         Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      mn-homo : IsMonoidMorphism F.monoid T.monoid ⟦_⟧

    open IsMonoidMorphism mn-homo public

    ⁻¹-homo : Homomorphic₁ ⟦_⟧ F._⁻¹ T._⁻¹
    ⁻¹-homo x = let open EqR T.setoid in T.uniqueˡ-⁻¹ ⟦ x F.⁻¹ ⟧ ⟦ x ⟧ $ begin
      ⟦ x F.⁻¹ ⟧ T.∙ ⟦ x ⟧ ≈⟨ T.sym (∙-homo (x F.⁻¹) x) ⟩
      ⟦ x F.⁻¹ F.∙ x ⟧     ≈⟨ ⟦⟧-cong (proj₁ F.inverse x) ⟩
      ⟦ F.ε ⟧              ≈⟨ ε-homo ⟩
      T.ε ∎

  syntax IsGroupMorphism From To F = F Is From -Group⟶ To

module _ {c₁ ℓ₁ c₂ ℓ₂}
         (From : AbelianGroup c₁ ℓ₁)
         (To   : AbelianGroup c₂ ℓ₂) where

  private
    module F = AbelianGroup From
    module T = AbelianGroup To
  open Definitions F.Carrier T.Carrier T._≈_

  record IsAbelianGroupMorphism (⟦_⟧ : Morphism) :
         Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      gp-homo : IsGroupMorphism F.group T.group ⟦_⟧

    open IsGroupMorphism gp-homo public

  syntax IsAbelianGroupMorphism From To F = F Is From -AbelianGroup⟶ To

module _ {c₁ ℓ₁ c₂ ℓ₂}
         (From : Ring c₁ ℓ₁)
         (To   : Ring c₂ ℓ₂) where

  private
    module F = Ring From
    module T = Ring To
  open Definitions F.Carrier T.Carrier T._≈_

  record IsRingMorphism (⟦_⟧ : Morphism) :
         Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      +-abgp-homo : ⟦_⟧ Is F.+-abelianGroup -AbelianGroup⟶ T.+-abelianGroup
      *-mn-homo   : ⟦_⟧ Is F.*-monoid -Monoid⟶ T.*-monoid

  syntax IsRingMorphism From To F = F Is From -Ring⟶ To
