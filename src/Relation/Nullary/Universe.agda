------------------------------------------------------------------------
-- A universe of proposition functors, along with some properties
------------------------------------------------------------------------

module Relation.Nullary.Universe where

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Simple
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)
open import Relation.Binary.Sum
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.FunctionSetoid
open import Data.Sum     as Sum  hiding (map)
open import Data.Product as Prod hiding (map)
open import Data.Function
open import Data.Empty
open import Category.Applicative
open import Category.Monad

infix  5 ¬¬_
infixr 4 _⇒_
infixr 3 _∧_
infixr 2 _∨_
infix  1 ⟨_⟩_≈_

-- The universe.

data PropF : Set₁ where
  Id   : PropF
  K    : (P : Set) → PropF
  _∨_  : (F₁ F₂ : PropF) → PropF
  _∧_  : (F₁ F₂ : PropF) → PropF
  _⇒_  : (P₁ : Set) (F₂ : PropF) → PropF
  ¬¬_  : (F : PropF) → PropF

⟦_⟧ : PropF → (Set → Set)
⟦ Id ⟧      = λ x → x
⟦ K P ⟧     = λ _ → P
⟦ F₁ ∨ F₂ ⟧ = λ x → ⟦ F₁ ⟧ x ⊎ ⟦ F₂ ⟧ x
⟦ F₁ ∧ F₂ ⟧ = λ x → ⟦ F₁ ⟧ x × ⟦ F₂ ⟧ x
⟦ P₁ ⇒ F₂ ⟧ = λ x → P₁       → ⟦ F₂ ⟧ x
⟦ ¬¬ F ⟧    = λ x → ¬ ¬ ⟦ F ⟧ x

-- Equalities for universe inhabitants.

Eq : (F : PropF) {P : Set} → Rel (⟦ F ⟧ P)
Eq Id        = _≡_
Eq (K P)     = _≡_
Eq (F₁ ∨ F₂) = Eq F₁ ⊎-Rel Eq F₂
Eq (F₁ ∧ F₂) = Eq F₁ ×-Rel Eq F₂
Eq (P₁ ⇒ F₂) = ≡↝ (λ _ → Eq F₂)
Eq (¬¬ F)    = Always

⟨_⟩_≈_ : (F : PropF) {P : Set} → Rel (⟦ F ⟧ P)
⟨_⟩_≈_ = Eq

isEquivalence : ∀ F {P} → IsEquivalence (Eq F {P})
isEquivalence Id        = PropEq.isEquivalence
isEquivalence (K P)     = PropEq.isEquivalence
isEquivalence (F₁ ∨ F₂) = isEquivalence F₁ ⊎-isEquivalence
                          isEquivalence F₂
isEquivalence (F₁ ∧ F₂) = isEquivalence F₁ ×-isEquivalence
                          isEquivalence F₂
isEquivalence (P₁ ⇒ F₂) = ≡↝-isEquivalence (λ _ → isEquivalence F₂)
isEquivalence (¬¬ F)    = Always-isEquivalence

-- ⟦ F ⟧ is functorial.

map : ∀ F {P Q} → (P → Q) → ⟦ F ⟧ P → ⟦ F ⟧ Q
map Id        f  p = f p
map (K P)     f  p = p
map (F₁ ∨ F₂) f FP = Sum.map  (map F₁ f) (map F₂ f) FP
map (F₁ ∧ F₂) f FP = Prod.map (map F₁ f) (map F₂ f) FP
map (P₁ ⇒ F₂) f FP = map F₂ f ∘ FP
map (¬¬ F)    f FP = ¬¬-map (map F f) FP

map-id : ∀ F {P} → ⟨ ⟦ F ⟧ P ⇒ F ⟩ map F id ≈ id
map-id Id        x        = refl
map-id (K P)     x        = refl
map-id (F₁ ∨ F₂) (inj₁ x) = ₁∼₁ (map-id F₁ x)
map-id (F₁ ∨ F₂) (inj₂ y) = ₂∼₂ (map-id F₂ y)
map-id (F₁ ∧ F₂) (x , y)  = (map-id F₁ x , map-id F₂ y)
map-id (P₁ ⇒ F₂) f        = λ x → map-id F₂ (f x)
map-id (¬¬ F)    ¬¬x      = _

map-∘ : ∀ F {P Q R} (f : Q → R) (g : P → Q) →
        ⟨ ⟦ F ⟧ P ⇒ F ⟩ map F f ∘ map F g ≈ map F (f ∘ g)
map-∘ Id        f g x        = refl
map-∘ (K P)     f g x        = refl
map-∘ (F₁ ∨ F₂) f g (inj₁ x) = ₁∼₁ (map-∘ F₁ f g x)
map-∘ (F₁ ∨ F₂) f g (inj₂ y) = ₂∼₂ (map-∘ F₂ f g y)
map-∘ (F₁ ∧ F₂) f g x        = (map-∘ F₁ f g (proj₁ x) ,
                                map-∘ F₂ f g (proj₂ x))
map-∘ (P₁ ⇒ F₂) f g h        = λ x → map-∘ F₂ f g (h x)
map-∘ (¬¬ F)    f g x        = _

-- A variant of sequence can be implemented for ⟦ F ⟧.

sequence : ∀ {AF} → RawApplicative AF →
           (AF ⊥ → ⊥) →
           ({A B : Set} → (A → AF B) → AF (A → B)) →
           ∀ F {P} → ⟦ F ⟧ (AF P) → AF (⟦ F ⟧ P)
sequence {AF} A extract-⊥ sequence-⇒ = helper
  where
  open RawApplicative A

  helper : ∀ F {P} → ⟦ F ⟧ (AF P) → AF (⟦ F ⟧ P)
  helper Id        x        = x
  helper (K P)     x        = pure x
  helper (F₁ ∨ F₂) (inj₁ x) = inj₁ <$> helper F₁ x
  helper (F₁ ∨ F₂) (inj₂ y) = inj₂ <$> helper F₂ y
  helper (F₁ ∧ F₂) (x , y)  = _,_  <$> helper F₁ x ⊛ helper F₂ y
  helper (P₁ ⇒ F₂) f        = sequence-⇒ (helper F₂ ∘ f)
  helper (¬¬ F)    x        =
    pure (λ ¬FP → x (λ fp → extract-⊥ (¬FP <$> helper F fp)))

-- Some lemmas about double negation.

open RawMonad ¬¬-Monad

¬¬-pull : ∀ F {P} → ⟦ F ⟧ (¬ ¬ P) → ¬ ¬ ⟦ F ⟧ P
¬¬-pull = sequence rawIApplicative
                   (λ f → f id)
                   (λ f g → g (λ x → ⊥-elim (f x (λ y → g (λ _ → y)))))

¬¬-remove : ∀ F {P} → ¬ ¬ ⟦ F ⟧ (¬ ¬ P) → ¬ ¬ ⟦ F ⟧ P
¬¬-remove F = ¬¬-drop ∘ ¬¬-pull (¬¬ F)
