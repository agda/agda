------------------------------------------------------------------------
-- A universe of proposition functors, along with some properties
------------------------------------------------------------------------

module Relation.Nullary.Universe where

open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Simple
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Sum
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.FunctionLifting
open import Data.Sum
open import Data.Product
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
  K    : (P : Set) -> PropF
  _∨_  : (F₁ F₂ : PropF) -> PropF
  _∧_  : (F₁ F₂ : PropF) -> PropF
  _⇒_  : (P₁ : Set) (F₂ : PropF) -> PropF
  ¬¬_  : (F : PropF) -> PropF

⟦_⟧ : PropF -> (Set -> Set)
⟦ Id ⟧      = \x -> x
⟦ K P ⟧     = \_ -> P
⟦ F₁ ∨ F₂ ⟧ = \x -> ⟦ F₁ ⟧ x ⊎  ⟦ F₂ ⟧ x
⟦ F₁ ∧ F₂ ⟧ = \x -> ⟦ F₁ ⟧ x ×  ⟦ F₂ ⟧ x
⟦ P₁ ⇒ F₂ ⟧ = \x -> P₁       -> ⟦ F₂ ⟧ x
⟦ ¬¬ F ⟧    = \x -> ¬ ¬ ⟦ F ⟧ x

-- Equalities for universe inhabitants.

Eq : (F : PropF) {P : Set} -> Rel (⟦ F ⟧ P)
Eq Id        = _≡_
Eq (K P)     = _≡_
Eq (F₁ ∨ F₂) = Eq F₁ ⊎-Rel Eq F₂
Eq (F₁ ∧ F₂) = Eq F₁ ×-Rel Eq F₂
Eq (P₁ ⇒ F₂) = ≡↝ (Eq F₂)
Eq (¬¬ F)    = Always

⟨_⟩_≈_ : (F : PropF) {P : Set} -> Rel (⟦ F ⟧ P)
⟨_⟩_≈_ = Eq

Eq-isEquivalence : forall F {P} -> IsEquivalence (Eq F {P})
Eq-isEquivalence Id        = ≡-isEquivalence
Eq-isEquivalence (K P)     = ≡-isEquivalence
Eq-isEquivalence (F₁ ∨ F₂) = Eq-isEquivalence F₁ ⊎-isEquivalence
                             Eq-isEquivalence F₂
Eq-isEquivalence (F₁ ∧ F₂) = Eq-isEquivalence F₁ ×-isEquivalence
                             Eq-isEquivalence F₂
Eq-isEquivalence (P₁ ⇒ F₂) = LiftEquiv≡ (Eq-isEquivalence F₂)
Eq-isEquivalence (¬¬ F)    = Always-isEquivalence

-- ⟦ F ⟧ is functorial.

map : forall F {P Q} -> (P -> Q) -> ⟦ F ⟧ P -> ⟦ F ⟧ Q
map Id        f  p = f p
map (K P)     f  p = p
map (F₁ ∨ F₂) f FP = map-⊎ (map F₁ f) (map F₂ f) FP
map (F₁ ∧ F₂) f FP = map-× (map F₁ f) (map F₂ f) FP
map (P₁ ⇒ F₂) f FP = map F₂ f ∘ FP
map (¬¬ F)    f FP = ¬¬-map (map F f) FP

map-id : forall F {P} -> ⟨ ⟦ F ⟧ P ⇒ F ⟩ map F id ≈ id
map-id Id        x        = ≡-refl
map-id (K P)     x        = ≡-refl
map-id (F₁ ∨ F₂) (inj₁ x) = ₁∼₁ (map-id F₁ x)
map-id (F₁ ∨ F₂) (inj₂ y) = ₂∼₂ (map-id F₂ y)
map-id (F₁ ∧ F₂) (x , y)  = (map-id F₁ x , map-id F₂ y)
map-id (P₁ ⇒ F₂) f        = \x -> map-id F₂ (f x)
map-id (¬¬ F)    ¬¬x      = _

map-∘ : forall F {P Q R} (f : Q -> R) (g : P -> Q) ->
        ⟨ ⟦ F ⟧ P ⇒ F ⟩ map F f ∘ map F g ≈ map F (f ∘ g)
map-∘ Id        f g x        = ≡-refl
map-∘ (K P)     f g x        = ≡-refl
map-∘ (F₁ ∨ F₂) f g (inj₁ x) = ₁∼₁ (map-∘ F₁ f g x)
map-∘ (F₁ ∨ F₂) f g (inj₂ y) = ₂∼₂ (map-∘ F₂ f g y)
map-∘ (F₁ ∧ F₂) f g x        = (map-∘ F₁ f g (proj₁ x) ,
                                map-∘ F₂ f g (proj₂ x))
map-∘ (P₁ ⇒ F₂) f g h        = \x -> map-∘ F₂ f g (h x)
map-∘ (¬¬ F)    f g x        = _

-- Some lemmas about double negation.

¬¬-pull : forall F {P} -> ⟦ F ⟧ (¬ ¬ P) -> ¬ ¬ ⟦ F ⟧ P
¬¬-pull Id        ¬¬P      ¬P  = ¬¬P ¬P
¬¬-pull (K P)     p        ¬P  = ¬P p
¬¬-pull (F₁ ∨ F₂) (inj₁ x) ¬FP = ¬¬-map (¬FP ∘ inj₁) (¬¬-pull F₁ x) id
¬¬-pull (F₁ ∨ F₂) (inj₂ y) ¬FP = ¬¬-map (¬FP ∘ inj₂) (¬¬-pull F₂ y) id
¬¬-pull (F₁ ∧ F₂) (x , y)  ¬FP = ¬¬-map ¬FP (lem (¬¬-pull F₁ x)
                                                 (¬¬-pull F₂ y)) id
  where
  lem : forall {P Q} -> ¬ ¬ P -> ¬ ¬ Q -> ¬ ¬ (P × Q)
  lem ¬¬P ¬¬Q ¬PQ = ¬¬P (\P -> ¬¬Q (\Q -> ¬PQ ((P , Q))))
¬¬-pull (P₁ ⇒ F₂) h ¬FP =
  ¬FP (\p₁ -> ⊥-elim (¬¬-pull F₂ (h p₁) (\F₂P -> ¬FP (\_ -> F₂P))))
¬¬-pull (¬¬ F) h ¬FP = ¬¬-map ¬FP (¬¬-map (¬¬-pull F) h) id

¬¬-remove : forall F {P} -> ¬ ¬ ⟦ F ⟧ (¬ ¬ P) -> ¬ ¬ ⟦ F ⟧ P
¬¬-remove F = ¬¬-drop ∘ ¬¬-pull (¬¬ F)
