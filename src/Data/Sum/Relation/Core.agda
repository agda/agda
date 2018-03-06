------------------------------------------------------------------------
-- The Agda standard library
--
-- Sums of binary relations
------------------------------------------------------------------------

module Data.Sum.Relation.Core where

open import Data.Sum
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤)
open import Data.Empty using (⊥)
open import Function using (_⟨_⟩_; _∘_; flip)
open import Level using (_⊔_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary

module _ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂} where

  ----------------------------------------------------------------------
  -- Generalised sum of relations

  data ⊎ʳ {ℓ₁ ℓ₂} (P : Set) (_∼₁_ : Rel A₁ ℓ₁) (_∼₂_ : Rel A₂ ℓ₂) :
          A₁ ⊎ A₂ → A₁ ⊎ A₂ → Set (a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂) where
    ₁∼₂ : ∀ {x y} (p : P)         → ⊎ʳ P _∼₁_ _∼₂_ (inj₁ x) (inj₂ y)
    ₁∼₁ : ∀ {x y} (x∼₁y : x ∼₁ y) → ⊎ʳ P _∼₁_ _∼₂_ (inj₁ x) (inj₁ y)
    ₂∼₂ : ∀ {x y} (x∼₂y : x ∼₂ y) → ⊎ʳ P _∼₁_ _∼₂_ (inj₂ x) (inj₂ y)

  ----------------------------------------------------------------------
  -- Helpers

  module _ {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {∼₂ : Rel A₂ ℓ₂} where

    drop-inj₁ : ∀ {P x y} → inj₁ x ⟨ ⊎ʳ P ∼₁ ∼₂ ⟩ inj₁ y → ∼₁ x y
    drop-inj₁ (₁∼₁ x∼y) = x∼y

    drop-inj₂ : ∀ {P x y} → inj₂ x ⟨ ⊎ʳ P ∼₁ ∼₂ ⟩ inj₂ y → ∼₂ x y
    drop-inj₂ (₂∼₂ x∼y) = x∼y

  ----------------------------------------------------------------------
  -- Some properties which are preserved by ⊎ʳ

  module _ {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {∼₂ : Rel A₂ ℓ₂} where

    _⊎-refl_ : Reflexive ∼₁ → Reflexive ∼₂ →
               ∀ {P} → Reflexive (⊎ʳ P ∼₁ ∼₂)
    refl₁ ⊎-refl refl₂ = refl
        where
      refl : Reflexive (⊎ʳ _ _ _)
      refl {x = inj₁ _} = ₁∼₁ refl₁
      refl {x = inj₂ _} = ₂∼₂ refl₂

    _⊎-transitive_ : Transitive ∼₁ → Transitive ∼₂ →
                     ∀ {P} → Transitive (⊎ʳ P ∼₁ ∼₂)
    trans₁ ⊎-transitive trans₂ = trans
         where
      trans : Transitive (⊎ʳ _ _ _)
      trans (₁∼₁ x∼y) (₁∼₁ y∼z) = ₁∼₁ (trans₁ x∼y y∼z)
      trans (₂∼₂ x∼y) (₂∼₂ y∼z) = ₂∼₂ (trans₂ x∼y y∼z)
      trans (₁∼₂ p)   (₂∼₂ _)     = ₁∼₂ p
      trans (₁∼₁ _)   (₁∼₂ p)     = ₁∼₂ p


    _⊎-asymmetric_ : Asymmetric ∼₁ → Asymmetric ∼₂ →
                     ∀ {P} → Asymmetric (⊎ʳ P ∼₁ ∼₂)
    asym₁ ⊎-asymmetric asym₂ = asym
        where
      asym : Asymmetric (⊎ʳ _ _ _)
      asym (₁∼₁ x<y) (₁∼₁ y<x) = asym₁ x<y y<x
      asym (₂∼₂ x<y) (₂∼₂ y<x) = asym₂ x<y y<x
      asym (₁∼₂ _)   ()

    ⊎-decidable : Decidable ∼₁ → Decidable ∼₂ →
                  ∀ {P} → (∀ {x y} → Dec (inj₁ x ⟨ ⊎ʳ P ∼₁ ∼₂ ⟩ inj₂ y)) →
                  Decidable (⊎ʳ P ∼₁ ∼₂)
    ⊎-decidable dec₁ dec₂ {P} dec₁₂ = dec
      where
      dec : Decidable (⊎ʳ P ∼₁ ∼₂)
      dec (inj₁ x) (inj₂ y) = dec₁₂
      dec (inj₂ x) (inj₁ y) = no (λ())
      dec (inj₁ x) (inj₁ y) with dec₁ x y
      ... | yes x∼y = yes (₁∼₁ x∼y)
      ... | no  x≁y = no (x≁y ∘ drop-inj₁)
      dec (inj₂ x) (inj₂ y) with dec₂ x y
      ... | yes x∼y = yes (₂∼₂ x∼y)
      ... | no  x≁y = no (x≁y ∘ drop-inj₂)

  module _ {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {≈₁ : Rel A₁ ℓ₂}
           {ℓ₃ ℓ₄} {∼₂ : Rel A₂ ℓ₃} {≈₂ : Rel A₂ ℓ₄} where

    _⊎-reflexive_ : ≈₁ ⇒ ∼₁ → ≈₂ ⇒ ∼₂ →
                    ∀ {P} → (⊎ʳ ⊥ ≈₁ ≈₂) ⇒ (⊎ʳ P ∼₁ ∼₂)
    refl₁ ⊎-reflexive refl₂ = refl
      where
      refl : (⊎ʳ _ _ _ ) ⇒ (⊎ʳ _ _ _)
      refl (₁∼₁ x₁≈y₁) = ₁∼₁ (refl₁ x₁≈y₁)
      refl (₂∼₂ x₂≈y₂) = ₂∼₂ (refl₂ x₂≈y₂)
      refl (₁∼₂ ())

    _⊎-irreflexive_ : Irreflexive ≈₁ ∼₁ → Irreflexive ≈₂ ∼₂ →
                      ∀ {P} → Irreflexive (⊎ʳ ⊥ ≈₁ ≈₂) (⊎ʳ P ∼₁ ∼₂)
    irrefl₁ ⊎-irreflexive irrefl₂ = irrefl
      where
      irrefl : Irreflexive (⊎ʳ ⊥ _ _) (⊎ʳ _ _ _)
      irrefl (₁∼₁ x₁≈y₁) (₁∼₁ x₁<y₁) = irrefl₁ x₁≈y₁ x₁<y₁
      irrefl (₂∼₂ x₂≈y₂) (₂∼₂ x₂<y₂) = irrefl₂ x₂≈y₂ x₂<y₂
      irrefl (₁∼₂ ())    _

    _⊎-antisymmetric_ : Antisymmetric ≈₁ ∼₁ → Antisymmetric ≈₂ ∼₂ →
                        ∀ {P} → Antisymmetric (⊎ʳ ⊥ ≈₁ ≈₂) (⊎ʳ P ∼₁ ∼₂)
    antisym₁ ⊎-antisymmetric antisym₂ = antisym
      where
      antisym : Antisymmetric (⊎ʳ ⊥ _ _) (⊎ʳ _ _ _)
      antisym (₁∼₁ x≤y) (₁∼₁ y≤x) = ₁∼₁ (antisym₁ x≤y y≤x)
      antisym (₂∼₂ x≤y) (₂∼₂ y≤x) = ₂∼₂ (antisym₂ x≤y y≤x)
      antisym (₁∼₂ _)   ()

    _⊎-≈-respects₂_ : ∼₁ Respects₂ ≈₁ → ∼₂ Respects₂ ≈₂ →
                      ∀ {P} → (⊎ʳ P ∼₁ ∼₂) Respects₂ (⊎ʳ ⊥ ≈₁ ≈₂)
    _⊎-≈-respects₂_ resp₁ resp₂ {P} = resp¹ , resp²
      where
      resp¹ : ∀ {x} → ((⊎ʳ P ∼₁ ∼₂) x) Respects (⊎ʳ ⊥ ≈₁ ≈₂)
      resp¹ (₁∼₁ y≈y') (₁∼₁ x∼y) = ₁∼₁ (proj₁ resp₁ y≈y' x∼y)
      resp¹ (₂∼₂ y≈y') (₂∼₂ x∼y) = ₂∼₂ (proj₁ resp₂ y≈y' x∼y)
      resp¹ (₂∼₂ y≈y') (₁∼₂ p)   = (₁∼₂ p)
      resp¹ (₁∼₂ ())   _

      resp² :  ∀ {y} → (flip (⊎ʳ P ∼₁ ∼₂) y) Respects (⊎ʳ ⊥ ≈₁ ≈₂)
      resp² (₁∼₁ x≈x') (₁∼₁ x∼y) = ₁∼₁ (proj₂ resp₁ x≈x' x∼y)
      resp² (₂∼₂ x≈x') (₂∼₂ x∼y) = ₂∼₂ (proj₂ resp₂ x≈x' x∼y)
      resp² (₁∼₁ x≈x') (₁∼₂ p)   = (₁∼₂ p)
      resp² (₁∼₂ ())   _
