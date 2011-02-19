------------------------------------------------------------------------
-- Pointwise lifting of relations to lists
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.List.Pointwise where

open import Function
open import Data.Product
open import Data.List
open import Level
open import Relation.Nullary
open import Relation.Binary renaming (Rel to Rel₂)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

private
 module Dummy {a} {A : Set a} where

  infixr 5 _∷_

  data Rel {ℓ} (_∼_ : Rel₂ A ℓ) : List A → List A → Set (ℓ ⊔ a) where
    []  : Rel _∼_ [] []
    _∷_ : ∀ {x xs y ys} (x∼y : x ∼ y) (xs∼ys : Rel _∼_ xs ys) →
          Rel _∼_ (x ∷ xs) (y ∷ ys)

  head : ∀ {ℓ} {_∼_ : Rel₂ A ℓ} {x y xs ys} →
         Rel _∼_ (x ∷ xs) (y ∷ ys) → x ∼ y
  head (x∼y ∷ xs∼ys) = x∼y

  tail : ∀ {ℓ} {_∼_ : Rel₂ A ℓ} {x y xs ys} →
         Rel _∼_ (x ∷ xs) (y ∷ ys) → Rel _∼_ xs ys
  tail (x∼y ∷ xs∼ys) = xs∼ys

  reflexive : ∀ {ℓ₁ ℓ₂} {_≈_ : Rel₂ A ℓ₁} {_∼_ : Rel₂ A ℓ₂} →
              _≈_ ⇒ _∼_ → Rel _≈_ ⇒ Rel _∼_
  reflexive ≈⇒∼ []            = []
  reflexive ≈⇒∼ (x≈y ∷ xs≈ys) = ≈⇒∼ x≈y ∷ reflexive ≈⇒∼ xs≈ys

  refl : ∀ {ℓ} {_∼_ : Rel₂ A ℓ} →
         Reflexive _∼_ → Reflexive (Rel _∼_)
  refl rfl {[]}     = []
  refl rfl {x ∷ xs} = rfl ∷ refl rfl

  symmetric : ∀ {ℓ} {_∼_ : Rel₂ A ℓ} →
              Symmetric _∼_ → Symmetric (Rel _∼_)
  symmetric sym []            = []
  symmetric sym (x∼y ∷ xs∼ys) = sym x∼y ∷ symmetric sym xs∼ys

  transitive : ∀ {ℓ} {_∼_ : Rel₂ A ℓ} →
               Transitive _∼_ → Transitive (Rel _∼_)
  transitive trans []            []            = []
  transitive trans (x∼y ∷ xs∼ys) (y∼z ∷ ys∼zs) =
    trans x∼y y∼z ∷ transitive trans xs∼ys ys∼zs

  antisymmetric : ∀ {ℓ₁ ℓ₂} {_≈_ : Rel₂ A ℓ₁} {_≤_ : Rel₂ A ℓ₂} →
                  Antisymmetric _≈_ _≤_ →
                  Antisymmetric (Rel _≈_) (Rel _≤_)
  antisymmetric antisym []            []            = []
  antisymmetric antisym (x∼y ∷ xs∼ys) (y∼x ∷ ys∼xs) =
    antisym x∼y y∼x ∷ antisymmetric antisym xs∼ys ys∼xs

  respects₂ : ∀ {ℓ₁ ℓ₂} {_≈_ : Rel₂ A ℓ₁} {_∼_ : Rel₂ A ℓ₂} →
              _∼_ Respects₂ _≈_ → (Rel _∼_) Respects₂ (Rel _≈_)
  respects₂ {_} {_} {_≈_} {_∼_} resp =
    (λ {xs} {ys} {zs} → resp¹ {xs} {ys} {zs}) ,
    (λ {xs} {ys} {zs} → resp² {xs} {ys} {zs})
    where
    resp¹ : ∀ {xs} → (Rel _∼_ xs) Respects (Rel _≈_)
    resp¹ []            []            = []
    resp¹ (x≈y ∷ xs≈ys) (z∼x ∷ zs∼xs) =
      proj₁ resp x≈y z∼x ∷ resp¹ xs≈ys zs∼xs

    resp² : ∀ {ys} → (flip (Rel _∼_) ys) Respects (Rel _≈_)
    resp² []            []            = []
    resp² (x≈y ∷ xs≈ys) (x∼z ∷ xs∼zs) =
      proj₂ resp x≈y x∼z ∷ resp² xs≈ys xs∼zs

  decidable : ∀ {ℓ} {_∼_ : Rel₂ A ℓ} →
              Decidable _∼_ → Decidable (Rel _∼_)
  decidable dec []       []       = yes []
  decidable dec []       (y ∷ ys) = no (λ ())
  decidable dec (x ∷ xs) []       = no (λ ())
  decidable dec (x ∷ xs) (y ∷ ys) with dec x y
  ... | no ¬x∼y = no (¬x∼y ∘ head)
  ... | yes x∼y with decidable dec xs ys
  ...           | no ¬xs∼ys = no (¬xs∼ys ∘ tail)
  ...           | yes xs∼ys = yes (x∼y ∷ xs∼ys)

  isEquivalence : ∀ {ℓ} {_≈_ : Rel₂ A ℓ} →
                  IsEquivalence _≈_ → IsEquivalence (Rel _≈_)
  isEquivalence eq = record
    { refl  = refl       Eq.refl
    ; sym   = symmetric  Eq.sym
    ; trans = transitive Eq.trans
    } where module Eq = IsEquivalence eq

  isPreorder : ∀ {ℓ₁ ℓ₂} {_≈_ : Rel₂ A ℓ₁} {_∼_ : Rel₂ A ℓ₂} →
               IsPreorder _≈_ _∼_ → IsPreorder (Rel _≈_) (Rel _∼_)
  isPreorder pre = record
    { isEquivalence = isEquivalence Pre.isEquivalence
    ; reflexive     = reflexive     Pre.reflexive
    ; trans         = transitive    Pre.trans
    } where module Pre = IsPreorder pre

  isDecEquivalence : ∀ {ℓ} {_≈_ : Rel₂ A ℓ} → IsDecEquivalence _≈_ →
                     IsDecEquivalence (Rel _≈_)
  isDecEquivalence eq = record
    { isEquivalence = isEquivalence Dec.isEquivalence
    ; _≟_           = decidable     Dec._≟_
    } where module Dec = IsDecEquivalence eq

  isPartialOrder : ∀ {ℓ₁ ℓ₂} {_≈_ : Rel₂ A ℓ₁} {_≤_ : Rel₂ A ℓ₂} →
                   IsPartialOrder _≈_ _≤_ →
                   IsPartialOrder (Rel _≈_) (Rel _≤_)
  isPartialOrder po = record
    { isPreorder = isPreorder    PO.isPreorder
    ; antisym    = antisymmetric PO.antisym
    } where module PO = IsPartialOrder po

  -- Rel _≡_ coincides with _≡_.

  Rel≡⇒≡ : Rel _≡_ ⇒ _≡_
  Rel≡⇒≡ []                    = PropEq.refl
  Rel≡⇒≡ (PropEq.refl ∷ xs∼ys) with Rel≡⇒≡ xs∼ys
  Rel≡⇒≡ (PropEq.refl ∷ xs∼ys) | PropEq.refl = PropEq.refl

  ≡⇒Rel≡ : _≡_ ⇒ Rel _≡_
  ≡⇒Rel≡ PropEq.refl = refl PropEq.refl

open Dummy public

preorder : ∀ {p₁ p₂ p₃} → Preorder p₁ p₂ p₃ → Preorder _ _ _
preorder p = record
  { isPreorder = isPreorder (Preorder.isPreorder p)
  }

setoid : ∀ {c ℓ} → Setoid c ℓ → Setoid _ _
setoid s = record
  { isEquivalence = isEquivalence (Setoid.isEquivalence s)
  }

decSetoid : ∀ {c ℓ} → DecSetoid c ℓ → DecSetoid _ _
decSetoid d = record
  { isDecEquivalence = isDecEquivalence (DecSetoid.isDecEquivalence d)
  }

poset : ∀ {c ℓ₁ ℓ₂} → Poset c ℓ₁ ℓ₂ → Poset _ _ _
poset p = record
  { isPartialOrder = isPartialOrder (Poset.isPartialOrder p)
  }
