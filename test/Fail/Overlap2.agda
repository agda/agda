module Overlap2 where

open Agda.Primitive renaming (Set to Type ; Setω to Typeω)
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

record Extensional {ℓ} (A : Type ℓ) (ℓ-rel : Level) : Type (ℓ ⊔ lsuc ℓ-rel) where
  no-eta-equality
  field Pathᵉ : A → A → Type ℓ-rel

open Extensional ⦃ ... ⦄ renaming (Pathᵉ to _∼_)
open Extensional

postulate instance
  Extensional-default : ∀ {ℓ} {A} → Extensional {ℓ} A ℓ

  Extensional-Π
    : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : A → Type ℓ'}
    → ⦃ sb : ∀ {x} → Extensional (B x) ℓr ⦄
    → Extensional ((x : A) → B x) (ℓ ⊔ ℓr)

  Extensional-uncurry
    : ∀ {ℓ ℓ' ℓ'' ℓr} {A : Type ℓ} {B : A → Type ℓ'} {C : Type ℓ''}
    → ⦃ sb : Extensional ((x : A) → B x → C) ℓr ⦄
    → Extensional (Σ A B → C) ℓr
  {-# OVERLAPPING Extensional-uncurry #-}

-- Extensional-uncurry is more specific than Extensional-Π, so -Π is
-- discarded. But it's not more specific than Extensional-default: there
-- is no way to unify
--
--    Extensional {ℓ ⊔ ℓ' ⊔ ℓ''} (Σ A B → C) ℓr  -- head of -uncurry ("rigid" variables)
--    Extensional {?0}           ?1          ?0  -- head of -default ("flex" variables)
--
-- So this instance constraint is blocked; but the error message should
-- not mention -Π, which has been discarded.

module _ {A B : Type} where
  _ : Type₁
  _ = {f g : (Σ A λ _ → A) → B} → (f ∼ g) ≡ ((x y : A) → f (x , y) ≡ g (x , y))
