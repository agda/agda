------------------------------------------------------------------------
-- Containers, based on the work of Abbott and others
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Data.Container where

open import Data.Product as Prod hiding (map)
open import Function renaming (id to ⟨id⟩; _∘_ to _⟨∘⟩_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_⇿_; module Inverse)
open import Level
open import Relation.Binary using (Setoid; module Setoid)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≗_; refl)
open import Relation.Unary using (_⊆_)

------------------------------------------------------------------------
-- Containers

-- A container is a set of shapes, and for every shape a set of
-- positions.

infix 5 _◃_

record Container (ℓ : Level) : Set (suc ℓ) where
  constructor _◃_
  field
    Shape    : Set ℓ
    Position : Shape → Set ℓ

open Container public

-- The semantics ("extension") of a container.

⟦_⟧ : ∀ {ℓ} → Container ℓ → Set ℓ → Set ℓ
⟦ C ⟧ X = Σ[ s ∶ Shape C ] (Position C s → X)

-- Equality, parametrised on an underlying relation.

Eq : ∀ {c ℓ} {C : Container c} {X Y : Set c} →
     (X → Y → Set ℓ) → ⟦ C ⟧ X → ⟦ C ⟧ Y → Set (c ⊔ ℓ)
Eq {C = C} _≈_ (s , f) (s′ , f′) =
  Σ[ eq ∶ s ≡ s′ ] (∀ p → f p ≈ f′ (P.subst (Position C) eq p))

private

  -- Note that, if propositional equality were extensional, then
  -- Eq _≡_ and _≡_ would coincide.

  Eq⇒≡ : ∀ {c} {C : Container c} {X : Set c} {xs ys : ⟦ C ⟧ X} →
         P.Extensionality c c → Eq _≡_ xs ys → xs ≡ ys
  Eq⇒≡ {C = C} {X} ext (s≡s′ , f≈f′) = helper s≡s′ f≈f′
    where
    helper : {s s′ : Shape C} (eq : s ≡ s′) →
             {f  : Position C s  → X}
             {f′ : Position C s′ → X} →
             (∀ p → f p ≡ f′ (P.subst (Position C) eq p)) →
             _≡_ {A = ⟦ C ⟧ X} (s , f) (s′ , f′)
    helper refl f≈f′ = P.cong (_,_ _) (ext f≈f′)

setoid : ∀ {ℓ} → Container ℓ → Setoid ℓ ℓ → Setoid ℓ ℓ
setoid C X = record
  { Carrier       = ⟦ C ⟧ X.Carrier
  ; _≈_           = _≈_
  ; isEquivalence = record
    { refl  = (refl , λ _ → X.refl)
    ; sym   = sym
    ; trans = λ {_ _ zs} → trans zs
    }
  }
  where
  module X = Setoid X

  _≈_ = Eq X._≈_

  sym : {xs ys : ⟦ C ⟧ X.Carrier} → xs ≈ ys → ys ≈ xs
  sym (eq , f) = helper eq f
    where
    helper : {s s′ : Shape C} (eq : s ≡ s′) →
             {f  : Position C s  → X.Carrier}
             {f′ : Position C s′ → X.Carrier} →
             (∀ p → X._≈_ (f p) (f′ $ P.subst (Position C) eq p)) →
             (s′ , f′) ≈ (s , f)
    helper refl eq = (refl , X.sym ⟨∘⟩ eq)

  trans : ∀ {xs ys : ⟦ C ⟧ X.Carrier} zs → xs ≈ ys → ys ≈ zs → xs ≈ zs
  trans zs (eq₁ , f₁) (eq₂ , f₂) = helper eq₁ eq₂ (proj₂ zs) f₁ f₂
    where
    helper : {s s′ s″ : Shape C} (eq₁ : s ≡ s′) (eq₂ : s′ ≡ s″) →
             {f  : Position C s  → X.Carrier}
             {f′ : Position C s′ → X.Carrier} →
             (f″ : Position C s″ → X.Carrier) →
             (∀ p → X._≈_ (f  p) (f′ $ P.subst (Position C) eq₁ p)) →
             (∀ p → X._≈_ (f′ p) (f″ $ P.subst (Position C) eq₂ p)) →
             (s , f) ≈ (s″ , f″)
    helper refl refl _ eq₁ eq₂ = (refl , λ p → X.trans (eq₁ p) (eq₂ p))

------------------------------------------------------------------------
-- Functoriality

-- Containers are functors.

map : ∀ {c} {C : Container c} {X Y} → (X → Y) → ⟦ C ⟧ X → ⟦ C ⟧ Y
map f = Prod.map ⟨id⟩ (λ g → f ⟨∘⟩ g)

module Map where

  identity : ∀ {c} {C : Container c} X →
             let module X = Setoid X in
             (xs : ⟦ C ⟧ X.Carrier) → Eq X._≈_ (map ⟨id⟩ xs) xs
  identity {C = C} X xs = Setoid.refl (setoid C X)

  composition : ∀ {c} {C : Container c} {X Y} Z →
                let module Z = Setoid Z in
                (f : Y → Z.Carrier) (g : X → Y) (xs : ⟦ C ⟧ X) →
                Eq Z._≈_ (map f (map g xs)) (map (f ⟨∘⟩ g) xs)
  composition {C = C} Z f g xs = Setoid.refl (setoid C Z)

------------------------------------------------------------------------
-- Container morphisms

-- Representation of container morphisms.

record _⇒_ {c} (C₁ C₂ : Container c) : Set c where
  field
    shape    : Shape C₁ → Shape C₂
    position : ∀ {s} → Position C₂ (shape s) → Position C₁ s

open _⇒_ public

-- Interpretation of _⇒_.

⟪_⟫ : ∀ {c} {C₁ C₂ : Container c} →
      C₁ ⇒ C₂ → ∀ {X} → ⟦ C₁ ⟧ X → ⟦ C₂ ⟧ X
⟪ m ⟫ xs = (shape m (proj₁ xs) , proj₂ xs ⟨∘⟩ position m)

module Morphism where

  -- Naturality.

  Natural : ∀ {c} {C₁ C₂ : Container c} →
            (∀ {X} → ⟦ C₁ ⟧ X → ⟦ C₂ ⟧ X) → Set (suc c)
  Natural {c} {C₁} m =
    ∀ {X} (Y : Setoid c c) → let module Y = Setoid Y in
    (f : X → Y.Carrier) (xs : ⟦ C₁ ⟧ X) →
    Eq Y._≈_ (m $ map f xs) (map f $ m xs)

  -- Natural transformations.

  NT : ∀ {c} (C₁ C₂ : Container c) → Set (suc c)
  NT C₁ C₂ = ∃ λ (m : ∀ {X} → ⟦ C₁ ⟧ X → ⟦ C₂ ⟧ X) → Natural m

  -- Container morphisms are natural.

  natural : ∀ {c} {C₁ C₂ : Container c}
            (m : C₁ ⇒ C₂) → Natural ⟪ m ⟫
  natural {C₂ = C₂} m Y f xs = Setoid.refl (setoid C₂ Y)

  -- In fact, all natural functions of the right type are container
  -- morphisms.

  complete : ∀ {c} {C₁ C₂ : Container c} →
             (nt : NT C₁ C₂) →
             ∃ λ m → (X : Setoid c c) →
                     let module X = Setoid X in
                     (xs : ⟦ C₁ ⟧ X.Carrier) →
                     Eq X._≈_ (proj₁ nt xs) (⟪ m ⟫ xs)
  complete (nt , nat) =
    (m , λ X xs → nat X (proj₂ xs) (proj₁ xs , ⟨id⟩))
    where
    m = record { shape    = λ  s  → proj₁ (nt (s , ⟨id⟩))
               ; position = λ {s} → proj₂ (nt (s , ⟨id⟩))
               }

  -- Identity.

  id : ∀ {c} (C : Container c) → C ⇒ C
  id _ = record {shape = ⟨id⟩; position = ⟨id⟩}

  -- Composition.

  infixr 9 _∘_

  _∘_ : ∀ {c} {C₁ C₂ C₃ : Container c} → C₂ ⇒ C₃ → C₁ ⇒ C₂ → C₁ ⇒ C₃
  f ∘ g = record
    { shape    = shape    f ⟨∘⟩ shape    g
    ; position = position g ⟨∘⟩ position f
    }

  -- Identity and composition commute with ⟪_⟫.

  id-correct : ∀ {c} {C : Container c} {X : Set c} →
               ⟪ id C ⟫ {X} ≗ ⟨id⟩
  id-correct xs = refl

  ∘-correct : ∀ {c} {C₁ C₂ C₃ : Container c}
              (f : C₂ ⇒ C₃) (g : C₁ ⇒ C₂) {X : Set c} →
              ⟪ f ∘ g ⟫ {X} ≗ (⟪ f ⟫ ⟨∘⟩ ⟪ g ⟫)
  ∘-correct f g xs = refl

------------------------------------------------------------------------
-- Linear container morphisms

record _⊸_ {c} (C₁ C₂ : Container c) : Set c where
  field
    shape⊸    : Shape C₁ → Shape C₂
    position⊸ : ∀ {s} → Position C₂ (shape⊸ s) ⇿ Position C₁ s

  morphism : C₁ ⇒ C₂
  morphism = record
    { shape    = shape⊸
    ; position = _⟨$⟩_ (Inverse.to position⊸)
    }

  ⟪_⟫⊸ : ∀ {X} → ⟦ C₁ ⟧ X → ⟦ C₂ ⟧ X
  ⟪_⟫⊸ = ⟪ morphism ⟫

open _⊸_ public using (shape⊸; position⊸; ⟪_⟫⊸)

------------------------------------------------------------------------
-- All and any

-- All.

□ : ∀ {c} {C : Container c} {X : Set c} →
    (X → Set c) → (⟦ C ⟧ X → Set c)
□ P (s , f) = ∀ p → P (f p)

□-map : ∀ {c} {C : Container c} {X : Set c} {P Q : X → Set c} →
        P ⊆ Q → □ {C = C} P ⊆ □ Q
□-map P⊆Q = _⟨∘⟩_ P⊆Q

-- Any.

◇ : ∀ {c} {C : Container c} {X : Set c} →
    (X → Set c) → (⟦ C ⟧ X → Set c)
◇ P (s , f) = ∃ λ p → P (f p)

◇-map : ∀ {c} {C : Container c} {X : Set c} {P Q : X → Set c} →
        P ⊆ Q → ◇ {C = C} P ⊆ ◇ Q
◇-map P⊆Q = Prod.map ⟨id⟩ P⊆Q

-- Membership.

infix 4 _∈_

_∈_ : ∀ {c} {C : Container c} {X : Set c} →
      X → ⟦ C ⟧ X → Set c
x ∈ xs = ◇ (_≡_ x) xs

-- Bag and set equality. Two containers xs and ys are equal when
-- viewed as sets if, whenever x ∈ xs, we also have x ∈ ys, and vice
-- versa. They are equal when viewed as bags if, additionally, the
-- sets x ∈ xs and x ∈ ys have the same size. For alternative but
-- equivalent definitions of bag and set equality, see
-- Data.Container.AlternativeBagAndSetEquality.

open Inv public
  using (Kind) renaming (inverse to bag; equivalent to set)

[_]-Equality : ∀ {ℓ} → Kind → Container ℓ → Set ℓ → Setoid ℓ ℓ
[ k ]-Equality C X = Inv.InducedEquivalence₂ k (_∈_ {C = C} {X = X})

infix 4 _≈[_]_

_≈[_]_ : ∀ {c} {C : Container c} {X : Set c} →
         ⟦ C ⟧ X → Kind → ⟦ C ⟧ X → Set c
xs ≈[ k ] ys = Setoid._≈_ ([ k ]-Equality _ _) xs ys
