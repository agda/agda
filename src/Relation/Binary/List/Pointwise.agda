------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of relations to lists
------------------------------------------------------------------------

module Relation.Binary.List.Pointwise where

open import Function
open import Function.Inverse using (Inverse)
open import Data.Product hiding (map)
open import Data.List.Base hiding (map)
open import Level
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec using (map′)
open import Relation.Binary renaming (Rel to Rel₂)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

infixr 5 _∷_

data Rel {a b ℓ} {A : Set a} {B : Set b}
         (_∼_ : REL A B ℓ) : List A → List B → Set (a ⊔ b ⊔ ℓ) where
  []  : Rel _∼_ [] []
  _∷_ : ∀ {x xs y ys} (x∼y : x ∼ y) (xs∼ys : Rel _∼_ xs ys) →
        Rel _∼_ (x ∷ xs) (y ∷ ys)

head : ∀ {a b ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ} {x y xs ys} →
       Rel _∼_ (x ∷ xs) (y ∷ ys) → x ∼ y
head (x∼y ∷ xs∼ys) = x∼y

tail : ∀ {a b ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ} {x y xs ys} →
       Rel _∼_ (x ∷ xs) (y ∷ ys) → Rel _∼_ xs ys
tail (x∼y ∷ xs∼ys) = xs∼ys

rec : ∀ {a b c ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ}
      (P : ∀ {xs ys} → Rel _∼_ xs ys → Set c) →
      (∀ {x y xs ys} {xs∼ys : Rel _∼_ xs ys} →
         (x∼y : x ∼ y) → P xs∼ys → P (x∼y ∷ xs∼ys)) →
      P [] →
      ∀ {xs ys} (xs∼ys : Rel _∼_ xs ys) → P xs∼ys
rec P c n []            = n
rec P c n (x∼y ∷ xs∼ys) = c x∼y (rec P c n xs∼ys)

map : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
        {_≈_ : REL A B ℓ₁} {_∼_ : REL A B ℓ₂} →
      _≈_ ⇒ _∼_ → Rel _≈_ ⇒ Rel _∼_
map ≈⇒∼ []            = []
map ≈⇒∼ (x≈y ∷ xs≈ys) = ≈⇒∼ x≈y ∷ map ≈⇒∼ xs≈ys

reflexive : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
              {_≈_ : REL A B ℓ₁} {_∼_ : REL A B ℓ₂} →
            _≈_ ⇒ _∼_ → Rel _≈_ ⇒ Rel _∼_
reflexive ≈⇒∼ []            = []
reflexive ≈⇒∼ (x≈y ∷ xs≈ys) = ≈⇒∼ x≈y ∷ reflexive ≈⇒∼ xs≈ys

refl : ∀ {a ℓ} {A : Set a} {_∼_ : Rel₂ A ℓ} →
       Reflexive _∼_ → Reflexive (Rel _∼_)
refl rfl {[]}     = []
refl rfl {x ∷ xs} = rfl ∷ refl rfl

symmetric : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
              {_≈_ : REL A B ℓ₁} {_∼_ : REL B A ℓ₂} →
            Sym _≈_ _∼_ → Sym (Rel _≈_) (Rel _∼_)
symmetric sym []            = []
symmetric sym (x∼y ∷ xs∼ys) = sym x∼y ∷ symmetric sym xs∼ys

transitive :
  ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c}
    {_≋_ : REL A B ℓ₁} {_≈_ : REL B C ℓ₂} {_∼_ : REL A C ℓ₃} →
  Trans _≋_ _≈_ _∼_ → Trans (Rel _≋_) (Rel _≈_) (Rel _∼_)
transitive trans []            []            = []
transitive trans (x∼y ∷ xs∼ys) (y∼z ∷ ys∼zs) =
  trans x∼y y∼z ∷ transitive trans xs∼ys ys∼zs

antisymmetric : ∀ {a ℓ₁ ℓ₂} {A : Set a}
                  {_≈_ : Rel₂ A ℓ₁} {_≤_ : Rel₂ A ℓ₂} →
                Antisymmetric _≈_ _≤_ →
                Antisymmetric (Rel _≈_) (Rel _≤_)
antisymmetric antisym []            []            = []
antisymmetric antisym (x∼y ∷ xs∼ys) (y∼x ∷ ys∼xs) =
  antisym x∼y y∼x ∷ antisymmetric antisym xs∼ys ys∼xs

respects₂ : ∀ {a ℓ₁ ℓ₂} {A : Set a}
              {_≈_ : Rel₂ A ℓ₁} {_∼_ : Rel₂ A ℓ₂} →
            _∼_ Respects₂ _≈_ → (Rel _∼_) Respects₂ (Rel _≈_)
respects₂ {_≈_ = _≈_} {_∼_} resp =
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

decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ} →
            Decidable _∼_ → Decidable (Rel _∼_)
decidable dec []       []       = yes []
decidable dec []       (y ∷ ys) = no (λ ())
decidable dec (x ∷ xs) []       = no (λ ())
decidable dec (x ∷ xs) (y ∷ ys) with dec x y
... | no ¬x∼y = no (¬x∼y ∘ head)
... | yes x∼y with decidable dec xs ys
...           | no ¬xs∼ys = no (¬xs∼ys ∘ tail)
...           | yes xs∼ys = yes (x∼y ∷ xs∼ys)

isEquivalence : ∀ {a ℓ} {A : Set a} {_≈_ : Rel₂ A ℓ} →
                IsEquivalence _≈_ → IsEquivalence (Rel _≈_)
isEquivalence eq = record
  { refl  = refl       Eq.refl
  ; sym   = symmetric  Eq.sym
  ; trans = transitive Eq.trans
  } where module Eq = IsEquivalence eq

isPreorder : ∀ {a ℓ₁ ℓ₂} {A : Set a}
               {_≈_ : Rel₂ A ℓ₁} {_∼_ : Rel₂ A ℓ₂} →
             IsPreorder _≈_ _∼_ → IsPreorder (Rel _≈_) (Rel _∼_)
isPreorder pre = record
  { isEquivalence = isEquivalence Pre.isEquivalence
  ; reflexive     = reflexive     Pre.reflexive
  ; trans         = transitive    Pre.trans
  } where module Pre = IsPreorder pre

isDecEquivalence : ∀ {a ℓ} {A : Set a}
                     {_≈_ : Rel₂ A ℓ} → IsDecEquivalence _≈_ →
                   IsDecEquivalence (Rel _≈_)
isDecEquivalence eq = record
  { isEquivalence = isEquivalence DE.isEquivalence
  ; _≟_           = decidable     DE._≟_
  } where module DE = IsDecEquivalence eq

isPartialOrder : ∀ {a ℓ₁ ℓ₂} {A : Set a}
                   {_≈_ : Rel₂ A ℓ₁} {_≤_ : Rel₂ A ℓ₂} →
                 IsPartialOrder _≈_ _≤_ →
                 IsPartialOrder (Rel _≈_) (Rel _≤_)
isPartialOrder po = record
  { isPreorder = isPreorder    PO.isPreorder
  ; antisym    = antisymmetric PO.antisym
  } where module PO = IsPartialOrder po

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

-- Rel _≡_ coincides with _≡_.

Rel≡⇒≡ : ∀ {a} {A : Set a} → Rel {A = A} _≡_ ⇒ _≡_
Rel≡⇒≡ []               = P.refl
Rel≡⇒≡ (P.refl ∷ xs∼ys) with Rel≡⇒≡ xs∼ys
Rel≡⇒≡ (P.refl ∷ xs∼ys) | P.refl = P.refl

≡⇒Rel≡ : ∀ {a} {A : Set a} → _≡_ ⇒ Rel {A = A} _≡_
≡⇒Rel≡ P.refl = refl P.refl

Rel↔≡ : ∀ {a} {A : Set a} →
        Inverse (setoid (P.setoid A)) (P.setoid (List A))
Rel↔≡ = record
  { to         = record { _⟨$⟩_ = id; cong = Rel≡⇒≡ }
  ; from       = record { _⟨$⟩_ = id; cong = ≡⇒Rel≡ }
  ; inverse-of = record
    { left-inverse-of  = λ _ → refl P.refl
    ; right-inverse-of = λ _ → P.refl
    }
  }

decidable-≡ : ∀ {a} {A : Set a} →
              Decidable {A = A} _≡_ → Decidable {A = List A} _≡_
decidable-≡ dec xs ys = Dec.map′ Rel≡⇒≡ ≡⇒Rel≡ (xs ≟ ys)
  where
  open DecSetoid (decSetoid (P.decSetoid dec))
