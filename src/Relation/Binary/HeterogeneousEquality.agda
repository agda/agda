------------------------------------------------------------------------
-- Heterogeneous equality
------------------------------------------------------------------------

module Relation.Binary.HeterogeneousEquality where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)
open import Data.Function
open import Data.Product

------------------------------------------------------------------------
-- Heterogeneous equality

infix 4 _≅_ _≇_ _≅₁_ _≇₁_

data _≅_ {a : Set} (x : a) : {b : Set} → b → Set where
  refl : x ≅ x

data _≅₁_ {a : Set₁} (x : a) : {b : Set₁} → b → Set where
  refl : x ≅₁ x

-- Nonequality.

_≇_ : {a : Set} → a → {b : Set} → b → Set
x ≇ y = ¬ x ≅ y

_≇₁_ : {a : Set₁} → a → {b : Set₁} → b → Set
x ≇₁ y = ¬ x ≅₁ y

------------------------------------------------------------------------
-- Conversion

≡-to-≅ : ∀ {a} {x y : a} → x ≡ y → x ≅ y
≡-to-≅ refl = refl

≅-to-≡ : ∀ {a} {x y : a} → x ≅ y → x ≡ y
≅-to-≡ refl = refl

------------------------------------------------------------------------
-- Some properties

reflexive : ∀ {a} → _⇒_ {a} _≡_ (λ x y → x ≅ y)
reflexive refl = refl

sym : ∀ {a b} {x : a} {y : b} → x ≅ y → y ≅ x
sym refl = refl

trans : ∀ {a b c} {x : a} {y : b} {z : c} → x ≅ y → y ≅ z → x ≅ z
trans refl refl = refl

subst : ∀ {a} → Substitutive {a} (λ x y → x ≅ y)
subst P refl p = p

subst₂ : ∀ {A B} (P : A → B → Set) →
         ∀ {x₁ x₂ y₁ y₂} → x₁ ≅ x₂ → y₁ ≅ y₂ → P x₁ y₁ → P x₂ y₂
subst₂ P refl refl p = p

subst₁ : ∀ {a} (P : a → Set₁) → ∀ {x y} → x ≅ y → P x → P y
subst₁ P refl p = p

subst-removable : ∀ {a} (P : a → Set) {x y} (eq : x ≅ y) z →
                  subst P eq z ≅ z
subst-removable P refl z = refl

≡-subst-removable : ∀ {a} (P : a → Set) {x y} (eq : x ≡ y) z →
                    PropEq.subst P eq z ≅ z
≡-subst-removable P refl z = refl

cong : ∀ {A : Set} {B : A → Set} {x y}
       (f : (x : A) → B x) → x ≅ y → f x ≅ f y
cong f refl = refl

cong₂ : ∀ {A : Set} {B : A → Set} {C : ∀ x → B x → Set} {x y u v}
        (f : (x : A) (y : B x) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
cong₂ f refl refl = refl

resp₂ : ∀ {a} (∼ : Rel a) → ∼ Respects₂ (λ x y → x ≅ y)
resp₂ _∼_ = subst⟶resp₂ _∼_ subst

isEquivalence : ∀ {a} → IsEquivalence {a} (λ x y → x ≅ y)
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

setoid : Set → Setoid
setoid a = record
  { carrier       = a
  ; _≈_           = λ x y → x ≅ y
  ; isEquivalence = isEquivalence
  }

decSetoid : ∀ {a} → Decidable (λ x y → _≅_ {a} x y) → DecSetoid
decSetoid dec = record
  { _≈_              = λ x y → x ≅ y
  ; isDecEquivalence = record
      { isEquivalence = isEquivalence
      ; _≟_           = dec
      }
  }

isPreorder : ∀ {a} → IsPreorder {a} (λ x y → x ≅ y) (λ x y → x ≅ y)
isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = id
  ; trans         = trans
  ; ∼-resp-≈      = resp₂ (λ x y → x ≅ y)
  }

isPreorder-≡ : ∀ {a} → IsPreorder {a} _≡_ (λ x y → x ≅ y)
isPreorder-≡ = record
  { isEquivalence = PropEq.isEquivalence
  ; reflexive     = reflexive
  ; trans         = trans
  ; ∼-resp-≈      = PropEq.resp₂ (λ x y → x ≅ y)
  }

preorder : Set → Preorder
preorder a = record
  { carrier    = a
  ; _≈_        = _≡_
  ; _∼_        = λ x y → x ≅ y
  ; isPreorder = isPreorder-≡
  }

------------------------------------------------------------------------
-- The inspect idiom

-- See Relation.Binary.PropositionalEquality.Inspect.

data Inspect {a : Set} (x : a) : Set where
  _with-≅_ : (y : a) (eq : y ≅ x) → Inspect x

inspect : ∀ {a} (x : a) → Inspect x
inspect x = x with-≅ refl

------------------------------------------------------------------------
-- Convenient syntax for equational reasoning

module ≅-Reasoning where

  -- The code in Relation.Binary.EqReasoning cannot handle
  -- heterogeneous equalities, hence the code duplication here.

  infix  4 _IsRelatedTo_
  infix  2 _∎
  infixr 2 _≅⟨_⟩_ _≡⟨_⟩_
  infix  1 begin_

  data _IsRelatedTo_ {A} (x : A) {B} (y : B) : Set where
    relTo : (x≅y : x ≅ y) → x IsRelatedTo y

  begin_ : ∀ {A} {x : A} {B} {y : B} → x IsRelatedTo y → x ≅ y
  begin relTo x≅y = x≅y

  _≅⟨_⟩_ : ∀ {A} (x : A) {B} {y : B} {C} {z : C} →
           x ≅ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≅⟨ x≅y ⟩ relTo y≅z = relTo (trans x≅y y≅z)

  _≡⟨_⟩_ : ∀ {A} (x : A) {y} {C} {z : C} →
           x ≡ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≡⟨ x≡y ⟩ relTo y≅z = relTo (trans (reflexive x≡y) y≅z)

  _∎ : ∀ {A} (x : A) → x IsRelatedTo x
  _∎ _ = relTo refl
