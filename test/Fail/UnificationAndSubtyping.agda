-- Jesper, 2017-01-23: when instantiating a variable during unification,
-- we should check that the type of the variable is equal to the type
-- of the equation (and not just a subtype of it). See Issue 2407.


{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Size

data D : Size → Set where

J= : ∀ {ℓ} {s : Size} (x₀ : D s)
   → (P : (x : D s) → _≡_ {A = D s} x₀ x → Set ℓ)
   → P x₀ refl → (x : D s) (e : _≡_ {A = D s} x₀ x) → P x e
J= _ P p _ refl = p

J< : ∀ {ℓ} {s : Size} {s' : Size< s} (x₀ : D s)
   → (P : (x : D s) → _≡_ {A = D s} x₀ x → Set ℓ)
   → P x₀ refl → (x : D s') (e : _≡_ {A = D s} x₀ x) → P x e
J< _ P p _ refl = p

J> : ∀ {ℓ} {s : Size} {s' : Size< s} (x₀ : D s')
   → (P : (x : D s) → _≡_ {A = D s} x₀ x → Set ℓ)
   → P x₀ refl → (x : D s) (e : _≡_ {A = D s} x₀ x) → P x e
J> _ P p _ refl = p

J~ : ∀ {ℓ} {s : Size} {s' s'' : Size< s} (x₀ : D s')
   → (P : (x : D s) → _≡_ {A = D s} x₀ x → Set ℓ)
   → P x₀ refl → (x : D s'') (e : _≡_ {A = D s} x₀ x) → P x e
J~ _ P p _ refl = p
