-- Andreas, 2026-11-07, extracted rose trees from standard-library.
-- An example for successor size termination that proves a property
-- about a sized function.
-- This is rejected by the semi-continuity check of PR #8895 as of 2026-11-06.
-- But it is an acceptable property with no termination problems.

{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Size
open import Agda.Builtin.List hiding (module List)
open import Agda.Builtin.Equality

-- Function combinators

infixr 9 _∘_ _∘′_
infixr -1 _$_

_∘_ : ∀ {A : Set} {B : A → Set} {C : {x : A} → B x → Set}
  → (∀ {x} (y : B x) → C y) → (g : (x : A) → B x)
  → ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

_∘′_ : {A B C : Set} → (B → C) → (A → B) → A → C
f ∘′ g = λ x → f (g x)

_$_ : {A : Set} {B : A → Set} → ((x : A) → B x) → (x : A) → B x
f $ x = f x

-- Equality

infix 4 _≗_

_≗_ : {A B : Set} (f g : A → B) → Set
f ≗ g = ∀ x → f x ≡ g x

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} (f : A → B → C) {x y : A} {u v : B}
  → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

module ≡-Reasoning {A : Set} where

  infix  3 _∎
  infixr 2 _≡⟨_⟩_
  infix  1 begin_

  begin_ : {x y : A} → x ≡ y → x ≡ y
  begin eq = eq

  _≡⟨_⟩_ : (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ eq ⟩ eq′ = trans eq eq′

  _∎ : (x : A) → x ≡ x
  x ∎ = refl

-- Lists

module List where

  map : {A B : Set} (f : A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  map-cong : {A B : Set} {f g : A → B} → f ≗ g → map f ≗ map g
  map-cong f≗g []       = refl
  map-cong f≗g (x ∷ xs) = cong₂ _∷_ (f≗g x) (map-cong f≗g xs)

  map-∘ : {A B C : Set} {g : B → C} {f : A → B}
    → map (g ∘ f) ≗ map g ∘ map f
  map-∘ []       = refl
  map-∘ (x ∷ xs) = cong (_ ∷_) (map-∘ xs)

-- Rose trees

data Rose (A : Set) : Size → Set where
  node : {i : Size} (a : A) (ts : List (Rose A i)) → Rose A (↑ i)

map : ∀ {i A B} → (A → B) → Rose A i → Rose B i
map f (node a ts) = node (f a) (List.map (map f) ts)

-- Second functor law

map-∘ : ∀{i A B C} (f : A → B) (g : B → C)
  → map {i = i} (g ∘′ f) ≗ map {i = i} g ∘′ map {i = i} f
map-∘ f g (node a ts) = cong (node (g (f a))) $ begin
  List.map (map (g ∘′ f)) ts             ≡⟨ List.map-cong (map-∘ f g) ts ⟩
  List.map (map g ∘ map f) ts            ≡⟨ List.map-∘ ts ⟩
  List.map (map g) (List.map (map f) ts) ∎
  where open ≡-Reasoning
