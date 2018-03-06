------------------------------------------------------------------------
-- The Agda standard library
--
-- A universe of proposition functors, along with some properties
------------------------------------------------------------------------

module Relation.Nullary.Universe where

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Simple
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)
open import Data.Sum     as Sum  hiding (map)
open import Data.Sum.Relation.General
open import Data.Product as Prod hiding (map)
open import Data.Product.Relation.Pointwise.NonDependent
open import Function
import Function.Equality as FunS
open import Data.Empty
open import Category.Applicative
open import Category.Monad
open import Level

infix  5 ¬¬_
infixr 4 _⇒_
infixr 3 _∧_
infixr 2 _∨_
infix  1 ⟨_⟩_≈_

-- The universe.

data PropF p : Set (suc p) where
  Id   : PropF p
  K    : (P : Set p) → PropF p
  _∨_  : (F₁ F₂ : PropF p) → PropF p
  _∧_  : (F₁ F₂ : PropF p) → PropF p
  _⇒_  : (P₁ : Set p) (F₂ : PropF p) → PropF p
  ¬¬_  : (F : PropF p) → PropF p

-- Equalities for universe inhabitants.

mutual

  setoid : ∀ {p} → PropF p → Set p → Setoid p p
  setoid Id        P = PropEq.setoid P
  setoid (K P)     _ = PropEq.setoid P
  setoid (F₁ ∨ F₂) P = (setoid F₁ P) ⊎-setoid (setoid F₂ P)
  setoid (F₁ ∧ F₂) P = (setoid F₁ P) ×ₛ (setoid F₂ P)
  setoid (P₁ ⇒ F₂) P = FunS.≡-setoid P₁
                         (Setoid.indexedSetoid (setoid F₂ P))
  setoid (¬¬ F)    P = Always-setoid (¬ ¬ ⟦ F ⟧ P)

  ⟦_⟧ : ∀ {p} → PropF p → (Set p → Set p)
  ⟦ F ⟧ P = Setoid.Carrier (setoid F P)

⟨_⟩_≈_ : ∀ {p} (F : PropF p) {P : Set p} → Rel (⟦ F ⟧ P) p
⟨_⟩_≈_ F = Setoid._≈_ (setoid F _)

-- ⟦ F ⟧ is functorial.

map : ∀ {p} (F : PropF p) {P Q} → (P → Q) → ⟦ F ⟧ P → ⟦ F ⟧ Q
map Id        f  p = f p
map (K P)     f  p = p
map (F₁ ∨ F₂) f FP = Sum.map  (map F₁ f) (map F₂ f) FP
map (F₁ ∧ F₂) f FP = Prod.map (map F₁ f) (map F₂ f) FP
map (P₁ ⇒ F₂) f FP = map F₂ f ∘ FP
map (¬¬ F)    f FP = ¬¬-map (map F f) FP

map-id : ∀ {p} (F : PropF p) {P} → ⟨ ⟦ F ⟧ P ⇒ F ⟩ map F id ≈ id
map-id Id        x        = refl
map-id (K P)     x        = refl
map-id (F₁ ∨ F₂) (inj₁ x) = ₁∼₁ (map-id F₁ x)
map-id (F₁ ∨ F₂) (inj₂ y) = ₂∼₂ (map-id F₂ y)
map-id (F₁ ∧ F₂) (x , y)  = (map-id F₁ x , map-id F₂ y)
map-id (P₁ ⇒ F₂) f        = λ x → map-id F₂ (f x)
map-id (¬¬ F)    ¬¬x      = _

map-∘ : ∀ {p} (F : PropF p) {P Q R} (f : Q → R) (g : P → Q) →
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

sequence : ∀ {p AF} → RawApplicative AF →
           (AF (Lift ⊥) → ⊥) →
           ({A B : Set p} → (A → AF B) → AF (A → B)) →
           ∀ F {P} → ⟦ F ⟧ (AF P) → AF (⟦ F ⟧ P)
sequence {AF = AF} A extract-⊥ sequence-⇒ = helper
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
    pure (λ ¬FP → x (λ fp → extract-⊥ (lift ∘ ¬FP <$> helper F fp)))

-- Some lemmas about double negation.

private
  open module M {p} = RawMonad (¬¬-Monad {p = p})

¬¬-pull : ∀ {p} (F : PropF p) {P} →
          ⟦ F ⟧ (¬ ¬ P) → ¬ ¬ ⟦ F ⟧ P
¬¬-pull = sequence rawIApplicative
                   (λ f → f lower)
                   (λ f g → g (λ x → ⊥-elim (f x (λ y → g (λ _ → y)))))

¬¬-remove : ∀ {p} (F : PropF p) {P} →
            ¬ ¬ ⟦ F ⟧ (¬ ¬ P) → ¬ ¬ ⟦ F ⟧ P
¬¬-remove F = negated-stable ∘ ¬¬-pull (¬¬ F)
