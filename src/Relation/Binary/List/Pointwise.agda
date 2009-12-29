------------------------------------------------------------------------
-- Pointwise lifting of relations to lists
------------------------------------------------------------------------

module Relation.Binary.List.Pointwise where

open import Function
open import Data.Product
open import Data.List
open import Level
open import Relation.Nullary
open import Relation.Binary renaming (Rel to Rel₂)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

private
 module Dummy {A : Set} where

  infixr 5 _∷_

  data Rel (_∼_ : Rel₂ A zero) : List A → List A → Set where
    []  : Rel _∼_ [] []
    _∷_ : ∀ {x xs y ys} (x∼y : x ∼ y) (xs∼ys : Rel _∼_ xs ys) →
          Rel _∼_ (x ∷ xs) (y ∷ ys)

  head : ∀ {_∼_ x y xs ys} → Rel _∼_ (x ∷ xs) (y ∷ ys) → x ∼ y
  head (x∼y ∷ xs∼ys) = x∼y

  tail : ∀ {_∼_ x y xs ys} → Rel _∼_ (x ∷ xs) (y ∷ ys) → Rel _∼_ xs ys
  tail (x∼y ∷ xs∼ys) = xs∼ys

  reflexive : ∀ {≈ ∼} → ≈ ⇒ ∼ → (Rel ≈) ⇒ (Rel ∼)
  reflexive ≈⇒∼ []            = []
  reflexive ≈⇒∼ (x≈y ∷ xs≈ys) = ≈⇒∼ x≈y ∷ reflexive ≈⇒∼ xs≈ys

  refl : ∀ {∼} → Reflexive ∼ → Reflexive (Rel ∼)
  refl rfl {[]}     = []
  refl rfl {x ∷ xs} = rfl ∷ refl rfl

  symmetric : ∀ {∼} → Symmetric ∼ → Symmetric (Rel ∼)
  symmetric sym []            = []
  symmetric sym (x∼y ∷ xs∼ys) = sym x∼y ∷ symmetric sym xs∼ys

  transitive : ∀ {∼} → Transitive ∼ → Transitive (Rel ∼)
  transitive trans []            []            = []
  transitive trans (x∼y ∷ xs∼ys) (y∼z ∷ ys∼zs) =
    trans x∼y y∼z ∷ transitive trans xs∼ys ys∼zs

  antisymmetric : ∀ {≈ ≤} → Antisymmetric ≈ ≤ →
                  Antisymmetric (Rel ≈) (Rel ≤)
  antisymmetric antisym []            []            = []
  antisymmetric antisym (x∼y ∷ xs∼ys) (y∼x ∷ ys∼xs) =
    antisym x∼y y∼x ∷ antisymmetric antisym xs∼ys ys∼xs

  respects₂ : ∀ {≈ ∼} → ∼ Respects₂ ≈ → (Rel ∼) Respects₂ (Rel ≈)
  respects₂ {≈} {∼} resp =
    (λ {xs} {ys} {zs} → resp¹ {xs} {ys} {zs}) ,
    (λ {xs} {ys} {zs} → resp² {xs} {ys} {zs})
    where
    resp¹ : ∀ {xs} → (Rel ∼ xs) Respects (Rel ≈)
    resp¹ []            []            = []
    resp¹ (x≈y ∷ xs≈ys) (z∼x ∷ zs∼xs) =
      proj₁ resp x≈y z∼x ∷ resp¹ xs≈ys zs∼xs

    resp² : ∀ {ys} → (flip (Rel ∼) ys) Respects (Rel ≈)
    resp² []            []            = []
    resp² (x≈y ∷ xs≈ys) (x∼z ∷ xs∼zs) =
      proj₂ resp x≈y x∼z ∷ resp² xs≈ys xs∼zs

  decidable : ∀ {∼} → Decidable ∼ → Decidable (Rel ∼)
  decidable dec []       []       = yes []
  decidable dec []       (y ∷ ys) = no (λ ())
  decidable dec (x ∷ xs) []       = no (λ ())
  decidable dec (x ∷ xs) (y ∷ ys) with dec x y
  ... | no ¬x∼y = no (¬x∼y ∘ head)
  ... | yes x∼y with decidable dec xs ys
  ...           | no ¬xs∼ys = no (¬xs∼ys ∘ tail)
  ...           | yes xs∼ys = yes (x∼y ∷ xs∼ys)

  isEquivalence : ∀ {≈} → IsEquivalence ≈ → IsEquivalence (Rel ≈)
  isEquivalence eq = record
    { refl  = refl       Eq.refl
    ; sym   = symmetric  Eq.sym
    ; trans = transitive Eq.trans
    } where module Eq = IsEquivalence eq

  isPreorder : ∀ {≈ ∼} → IsPreorder ≈ ∼ → IsPreorder (Rel ≈) (Rel ∼)
  isPreorder pre = record
    { isEquivalence = isEquivalence Pre.isEquivalence
    ; reflexive     = reflexive     Pre.reflexive
    ; trans         = transitive    Pre.trans
    ; ∼-resp-≈      = respects₂     Pre.∼-resp-≈
    } where module Pre = IsPreorder pre

  isDecEquivalence : ∀ {≈} → IsDecEquivalence ≈ →
                     IsDecEquivalence (Rel ≈)
  isDecEquivalence eq = record
    { isEquivalence = isEquivalence Dec.isEquivalence
    ; _≟_           = decidable     Dec._≟_
    } where module Dec = IsDecEquivalence eq

  isPartialOrder : ∀ {≈ ≤} → IsPartialOrder ≈ ≤ →
                   IsPartialOrder (Rel ≈) (Rel ≤)
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

preorder : Preorder _ _ _ → Preorder _ _ _
preorder p = record
  { isPreorder = isPreorder (Preorder.isPreorder p)
  }

setoid : Setoid _ _ → Setoid _ _
setoid s = record
  { isEquivalence = isEquivalence (Setoid.isEquivalence s)
  }

decSetoid : DecSetoid _ _ → DecSetoid _ _
decSetoid d = record
  { isDecEquivalence = isDecEquivalence (DecSetoid.isDecEquivalence d)
  }

poset : Poset _ _ _ → Poset _ _ _
poset p = record
  { isPartialOrder = isPartialOrder (Poset.isPartialOrder p)
  }
