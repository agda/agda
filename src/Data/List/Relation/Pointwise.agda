------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of relations to lists
------------------------------------------------------------------------

module Data.List.Relation.Pointwise where

open import Function
open import Function.Inverse using (Inverse)
open import Data.Product hiding (map)
open import Data.List.Base hiding (map)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Level
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec using (map′)
open import Relation.Binary renaming (Rel to Rel₂)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

infixr 5 _∷_

data Pointwise {a b ℓ} {A : Set a} {B : Set b}
         (_∼_ : REL A B ℓ) : List A → List B → Set ℓ where
  []  : Pointwise _∼_ [] []
  _∷_ : ∀ {x xs y ys} (x∼y : x ∼ y) (xs∼ys : Pointwise _∼_ xs ys) →
        Pointwise _∼_ (x ∷ xs) (y ∷ ys)

------------------------------------------------------------------------
-- Operations

module _ {a b ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ} where

  head : ∀ {x y xs ys} → Pointwise _∼_ (x ∷ xs) (y ∷ ys) → x ∼ y
  head (x∼y ∷ xs∼ys) = x∼y

  tail : ∀ {x y xs ys} → Pointwise _∼_ (x ∷ xs) (y ∷ ys) →
         Pointwise _∼_ xs ys
  tail (x∼y ∷ xs∼ys) = xs∼ys

  rec : ∀ {c} (P : ∀ {xs ys} → Pointwise _∼_ xs ys → Set c) →
        (∀ {x y xs ys} {xs∼ys : Pointwise _∼_ xs ys} →
          (x∼y : x ∼ y) → P xs∼ys → P (x∼y ∷ xs∼ys)) →
        P [] →
        ∀ {xs ys} (xs∼ys : Pointwise _∼_ xs ys) → P xs∼ys
  rec P c n []            = n
  rec P c n (x∼y ∷ xs∼ys) = c x∼y (rec P c n xs∼ys)

  map : ∀ {ℓ₂} {_≈_ : REL A B ℓ₂} →
        _≈_ ⇒ _∼_ → Pointwise _≈_ ⇒ Pointwise _∼_
  map ≈⇒∼ []            = []
  map ≈⇒∼ (x≈y ∷ xs≈ys) = ≈⇒∼ x≈y ∷ map ≈⇒∼ xs≈ys

------------------------------------------------------------------------
-- Relational properties

reflexive : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
            {_≈_ : REL A B ℓ₁} {_∼_ : REL A B ℓ₂} →
            _≈_ ⇒ _∼_ → Pointwise _≈_ ⇒ Pointwise _∼_
reflexive ≈⇒∼ []            = []
reflexive ≈⇒∼ (x≈y ∷ xs≈ys) = ≈⇒∼ x≈y ∷ reflexive ≈⇒∼ xs≈ys

refl : ∀ {a ℓ} {A : Set a} {_∼_ : Rel₂ A ℓ} →
       Reflexive _∼_ → Reflexive (Pointwise _∼_)
refl rfl {[]}     = []
refl rfl {x ∷ xs} = rfl ∷ refl rfl

symmetric : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
            {_≈_ : REL A B ℓ₁} {_∼_ : REL B A ℓ₂} →
            Sym _≈_ _∼_ → Sym (Pointwise _≈_) (Pointwise _∼_)
symmetric sym []            = []
symmetric sym (x∼y ∷ xs∼ys) = sym x∼y ∷ symmetric sym xs∼ys

transitive : ∀ {a b c ℓ₁ ℓ₂ ℓ₃}
             {A : Set a} {B : Set b} {C : Set c}
             {_≋_ : REL A B ℓ₁} {_≈_ : REL B C ℓ₂} {_∼_ : REL A C ℓ₃} →
             Trans _≋_ _≈_ _∼_ →
             Trans (Pointwise _≋_) (Pointwise _≈_) (Pointwise _∼_)
transitive trans []            []            = []
transitive trans (x∼y ∷ xs∼ys) (y∼z ∷ ys∼zs) =
  trans x∼y y∼z ∷ transitive trans xs∼ys ys∼zs

antisymmetric : ∀ {a ℓ₁ ℓ₂} {A : Set a}
                {_≈_ : Rel₂ A ℓ₁} {_≤_ : Rel₂ A ℓ₂} →
                Antisymmetric _≈_ _≤_ →
                Antisymmetric (Pointwise _≈_) (Pointwise _≤_)
antisymmetric antisym []            []            = []
antisymmetric antisym (x∼y ∷ xs∼ys) (y∼x ∷ ys∼xs) =
  antisym x∼y y∼x ∷ antisymmetric antisym xs∼ys ys∼xs

respects₂ : ∀ {a ℓ₁ ℓ₂} {A : Set a}
            {_≈_ : Rel₂ A ℓ₁} {_∼_ : Rel₂ A ℓ₂} →
            _∼_ Respects₂ _≈_ →
            (Pointwise _∼_) Respects₂ (Pointwise _≈_)
respects₂ {_≈_ = _≈_} {_∼_} resp = resp¹ , resp²
  where
  resp¹ : ∀ {xs} → (Pointwise _∼_ xs) Respects (Pointwise _≈_)
  resp¹ []            []            = []
  resp¹ (x≈y ∷ xs≈ys) (z∼x ∷ zs∼xs) =
    proj₁ resp x≈y z∼x ∷ resp¹ xs≈ys zs∼xs

  resp² : ∀ {ys} → (flip (Pointwise _∼_) ys) Respects (Pointwise _≈_)
  resp² []            []            = []
  resp² (x≈y ∷ xs≈ys) (x∼z ∷ xs∼zs) =
    proj₂ resp x≈y x∼z ∷ resp² xs≈ys xs∼zs

decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ} →
            Decidable _∼_ → Decidable (Pointwise _∼_)
decidable dec []       []       = yes []
decidable dec []       (y ∷ ys) = no (λ ())
decidable dec (x ∷ xs) []       = no (λ ())
decidable dec (x ∷ xs) (y ∷ ys) with dec x y
... | no ¬x∼y = no (¬x∼y ∘ head)
... | yes x∼y with decidable dec xs ys
...   | no ¬xs∼ys = no (¬xs∼ys ∘ tail)
...   | yes xs∼ys = yes (x∼y ∷ xs∼ys)

isEquivalence : ∀ {a ℓ} {A : Set a} {_≈_ : Rel₂ A ℓ} →
                IsEquivalence _≈_ → IsEquivalence (Pointwise _≈_)
isEquivalence eq = record
  { refl  = refl       Eq.refl
  ; sym   = symmetric  Eq.sym
  ; trans = transitive Eq.trans
  } where module Eq = IsEquivalence eq

isPreorder : ∀ {a ℓ₁ ℓ₂} {A : Set a}
             {_≈_ : Rel₂ A ℓ₁} {_∼_ : Rel₂ A ℓ₂} →
             IsPreorder _≈_ _∼_ → IsPreorder (Pointwise _≈_) (Pointwise _∼_)
isPreorder pre = record
  { isEquivalence = isEquivalence Pre.isEquivalence
  ; reflexive     = reflexive     Pre.reflexive
  ; trans         = transitive    Pre.trans
  } where module Pre = IsPreorder pre

isPartialOrder : ∀ {a ℓ₁ ℓ₂} {A : Set a}
                 {_≈_ : Rel₂ A ℓ₁} {_≤_ : Rel₂ A ℓ₂} →
                 IsPartialOrder _≈_ _≤_ →
                 IsPartialOrder (Pointwise _≈_) (Pointwise _≤_)
isPartialOrder po = record
  { isPreorder = isPreorder    PO.isPreorder
  ; antisym    = antisymmetric PO.antisym
  } where module PO = IsPartialOrder po

isDecEquivalence : ∀ {a ℓ} {A : Set a} {_≈_ : Rel₂ A ℓ} →
                   IsDecEquivalence _≈_ →
                   IsDecEquivalence (Pointwise _≈_)
isDecEquivalence eq = record
  { isEquivalence = isEquivalence DE.isEquivalence
  ; _≟_           = decidable     DE._≟_
  } where module DE = IsDecEquivalence eq

preorder : ∀ {p₁ p₂ p₃} → Preorder p₁ p₂ p₃ → Preorder _ _ _
preorder p = record
  { isPreorder = isPreorder (Preorder.isPreorder p)
  }

poset : ∀ {c ℓ₁ ℓ₂} → Poset c ℓ₁ ℓ₂ → Poset _ _ _
poset p = record
  { isPartialOrder = isPartialOrder (Poset.isPartialOrder p)
  }

setoid : ∀ {c ℓ} → Setoid c ℓ → Setoid _ _
setoid s = record
  { isEquivalence = isEquivalence (Setoid.isEquivalence s)
  }

decSetoid : ∀ {c ℓ} → DecSetoid c ℓ → DecSetoid _ _
decSetoid d = record
  { isDecEquivalence = isDecEquivalence (DecSetoid.isDecEquivalence d)
  }

------------------------------------------------------------------------
-- tabulate

module _ {a b ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} {g : Fin n → B} →
              (∀ i → f i ∼ g i) → Pointwise _∼_ (tabulate f) (tabulate g)
  tabulate⁺ {zero}  f∼g = []
  tabulate⁺ {suc n} f∼g = f∼g fzero ∷ tabulate⁺ (f∼g ∘ fsuc)

  tabulate⁻ : ∀ {n} {f : Fin n → A} {g : Fin n → B} →
              Pointwise _∼_ (tabulate f) (tabulate g) → (∀ i → f i ∼ g i)
  tabulate⁻ {zero}  []            ()
  tabulate⁻ {suc n} (x∼y ∷ xs∼ys) fzero    = x∼y
  tabulate⁻ {suc n} (x∼y ∷ xs∼ys) (fsuc i) = tabulate⁻ xs∼ys i

------------------------------------------------------------------------
-- _++_

module _ {a b ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ} where

  ++⁺ : ∀ {ws xs ys zs} → Pointwise _∼_ ws xs → Pointwise _∼_ ys zs →
        Pointwise _∼_ (ws ++ ys) (xs ++ zs)
  ++⁺ []            ys∼zs = ys∼zs
  ++⁺ (w∼x ∷ ws∼xs) ys∼zs = w∼x ∷ ++⁺ ws∼xs ys∼zs

------------------------------------------------------------------------
-- concat

module _ {a b ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ} where

  concat⁺ : ∀ {xss yss} → Pointwise (Pointwise _∼_) xss yss →
            Pointwise _∼_ (concat xss) (concat yss)
  concat⁺ []                = []
  concat⁺ (xs∼ys ∷ xss∼yss) = ++⁺ xs∼ys (concat⁺ xss∼yss)

------------------------------------------------------------------------
-- Properties of propositional pointwise

module _ {a} {A : Set a} where

  Pointwise-≡⇒≡ : Pointwise {A = A} _≡_ ⇒ _≡_
  Pointwise-≡⇒≡ []               = P.refl
  Pointwise-≡⇒≡ (P.refl ∷ xs∼ys) with Pointwise-≡⇒≡ xs∼ys
  ... | P.refl = P.refl

  ≡⇒Pointwise-≡ :  _≡_ ⇒ Pointwise {A = A} _≡_
  ≡⇒Pointwise-≡ P.refl = refl P.refl

  Pointwise-≡⇔≡ : Inverse (setoid (P.setoid A)) (P.setoid (List A))
  Pointwise-≡⇔≡ = record
    { to         = record { _⟨$⟩_ = id; cong = Pointwise-≡⇒≡ }
    ; from       = record { _⟨$⟩_ = id; cong = ≡⇒Pointwise-≡ }
    ; inverse-of = record
      { left-inverse-of  = λ _ → refl P.refl
      ; right-inverse-of = λ _ → P.refl
      }
    }

  decidable-≡ : Decidable {A = A} _≡_ → Decidable {A = List A} _≡_
  decidable-≡ dec xs ys = Dec.map′ Pointwise-≡⇒≡ ≡⇒Pointwise-≡ (xs ≟ ys)
    where
    open DecSetoid (decSetoid (P.decSetoid dec))

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

Rel    = Pointwise
Rel≡⇒≡ = Pointwise-≡⇒≡
≡⇒Rel≡ = ≡⇒Pointwise-≡
Rel↔≡  = Pointwise-≡⇔≡
