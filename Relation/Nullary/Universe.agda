------------------------------------------------------------------------
-- A universe of proposition functors, along with some properties
------------------------------------------------------------------------

module Relation.Nullary.Universe where

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Simple
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl)
open import Relation.Binary.Sum
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.FunctionLifting
import Data.Sum     as Sum;  open Sum  hiding (map)
import Data.Product as Prod; open Prod hiding (map)
open import Data.Function
open import Data.Empty

infix  5 ¬¬_
infixr 4 _⇒_
infixr 3 _∧_
infixr 2 _∨_
infix  1 ⟨_⟩_≈_

-- The universe.

data PropF : Set1 where
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
Eq (P₁ ⇒ F₂) = ≡↝ (Eq F₂)
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
isEquivalence (P₁ ⇒ F₂) = LiftEquiv≡ (isEquivalence F₂)
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

-- Some lemmas about double negation.

¬¬-pull : ∀ F {P} → ⟦ F ⟧ (¬ ¬ P) → ¬ ¬ ⟦ F ⟧ P
¬¬-pull Id        ¬¬P      ¬P  = ¬¬P ¬P
¬¬-pull (K P)     p        ¬P  = ¬P p
¬¬-pull (F₁ ∨ F₂) (inj₁ x) ¬FP = ¬¬-map (¬FP ∘ inj₁) (¬¬-pull F₁ x) id
¬¬-pull (F₁ ∨ F₂) (inj₂ y) ¬FP = ¬¬-map (¬FP ∘ inj₂) (¬¬-pull F₂ y) id
¬¬-pull (F₁ ∧ F₂) (x , y)  ¬FP = ¬¬-map ¬FP (lem (¬¬-pull F₁ x)
                                                 (¬¬-pull F₂ y)) id
  where
  lem : ∀ {P Q} → ¬ ¬ P → ¬ ¬ Q → ¬ ¬ (P × Q)
  lem ¬¬P ¬¬Q ¬PQ = ¬¬P (λ P → ¬¬Q (λ Q → ¬PQ ((P , Q))))
¬¬-pull (P₁ ⇒ F₂) h ¬FP =
  ¬FP (λ p₁ → ⊥-elim (¬¬-pull F₂ (h p₁) (λ F₂P → ¬FP (λ _ → F₂P))))
¬¬-pull (¬¬ F) h ¬FP = ¬¬-map ¬FP (¬¬-map (¬¬-pull F) h) id

¬¬-remove : ∀ F {P} → ¬ ¬ ⟦ F ⟧ (¬ ¬ P) → ¬ ¬ ⟦ F ⟧ P
¬¬-remove F = ¬¬-drop ∘ ¬¬-pull (¬¬ F)
