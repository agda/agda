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
⟦ C ⟧ X = ∃ λ (s : Shape C) → Position C s → X

-- Equality (based on propositional equality).

infix 4 _≈_

_≈_ : ∀ {c} {C : Container c} {X : Set c} → ⟦ C ⟧ X → ⟦ C ⟧ X → Set c
_≈_ {C = C} xs ys =
  ∃ λ (eq : proj₁ xs ≡ proj₁ ys) →
    ∀ p → proj₂ xs p ≡ proj₂ ys (P.subst (Position C) eq p)

private

  -- Note that, if propositional equality were extensional, _≈_ and
  -- _≡_ would coincide.

  ≈⇒≡ : ∀ {c} {C : Container c} {X : Set c} {xs ys : ⟦ C ⟧ X} →
        P.Extensionality c → xs ≈ ys → xs ≡ ys
  ≈⇒≡ {xs = s , f} {ys = .s , g} ext (refl , f≈g) =
    P.cong (_,_ s) (ext f≈g)

setoid : ∀ {ℓ} → Container ℓ → Set ℓ → Setoid ℓ ℓ
setoid C X = record
  { Carrier       = ⟦ C ⟧ X
  ; _≈_           = _≈_
  ; isEquivalence = record
    { refl  = (refl , λ _ → refl)
    ; sym   = sym
    ; trans = λ {_ _ zs} → trans {zs = zs}
    }
  }
  where
  sym : {xs ys : ⟦ C ⟧ X} → xs ≈ ys → ys ≈ xs
  sym {_ , _} {._ , _} (refl , f) = (refl , P.sym ⟨∘⟩ f)

  trans : {xs ys zs : ⟦ C ⟧ X} → xs ≈ ys → ys ≈ zs → xs ≈ zs
  trans {_ , _} {._ , _} {._ , _} (refl , f) (refl , g) =
    (refl , λ p → P.trans (f p) (g p))

------------------------------------------------------------------------
-- Functoriality

-- Containers are functors.

map : ∀ {c} {C : Container c} {X Y} → (X → Y) → ⟦ C ⟧ X → ⟦ C ⟧ Y
map f = Prod.map ⟨id⟩ (λ g → f ⟨∘⟩ g)

module Map where

  identity : ∀ {c} {C : Container c} {X}
             (xs : ⟦ C ⟧ X) → map ⟨id⟩ xs ≈ xs
  identity {C = C} xs = Setoid.refl (setoid C _)

  composition : ∀ {c} {C : Container c} {X Y Z}
                (f : Y → Z) (g : X → Y) (xs : ⟦ C ⟧ X) →
                map f (map g xs) ≈ map (f ⟨∘⟩ g) xs
  composition {C = C} f g xs = Setoid.refl (setoid C _)

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
  Natural {C₁ = C₁} m =
    ∀ {X Y} (f : X → Y) (xs : ⟦ C₁ ⟧ X) →
    m (map f xs) ≈ map f (m xs)

  -- Natural transformations.

  NT : ∀ {c} (C₁ C₂ : Container c) → Set (suc c)
  NT C₁ C₂ = ∃ λ (m : ∀ {X} → ⟦ C₁ ⟧ X → ⟦ C₂ ⟧ X) → Natural m

  -- Container morphisms are natural.

  natural : ∀ {c} {C₁ C₂ : Container c}
            (m : C₁ ⇒ C₂) → Natural ⟪ m ⟫
  natural {C₂ = C₂} m f xs = Setoid.refl (setoid C₂ _)

  -- In fact, all natural functions of the right type are container
  -- morphisms.

  complete : ∀ {c} {C₁ C₂ : Container c} →
             (nt : NT C₁ C₂) →
             ∃ λ m → ∀ {X} (xs : ⟦ C₁ ⟧ X) → proj₁ nt xs ≈ ⟪ m ⟫ xs
  complete (nt , nat) = (m , λ xs → nat (proj₂ xs) (proj₁ xs , ⟨id⟩))
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
□ P xs = ∀ p → P (proj₂ xs p)

□-map : ∀ {c} {C : Container c} {X : Set c} {P Q : X → Set c} →
        P ⊆ Q → □ {C = C} P ⊆ □ Q
□-map P⊆Q = _⟨∘⟩_ P⊆Q

-- Any.

◇ : ∀ {c} {C : Container c} {X : Set c} →
    (X → Set c) → (⟦ C ⟧ X → Set c)
◇ P xs = ∃ λ p → P (proj₂ xs p)

◇-map : ∀ {c} {C : Container c} {X : Set c} {P Q : X → Set c} →
        P ⊆ Q → ◇ {C = C} P ⊆ ◇ Q
◇-map P⊆Q = Prod.map ⟨id⟩ P⊆Q

-- Membership.

infix 4 _∈_

_∈_ : ∀ {c} {C : Container c} {X : Set c} →
      X → ⟦ C ⟧ X → Set c
x ∈ xs = ◇ (Lift ⟨∘⟩ _≡_ x) xs

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
