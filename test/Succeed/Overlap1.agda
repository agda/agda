module Overlap1 where

open Agda.Primitive renaming (Set to Type ; Setω to Typeω)
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

record Extensional {ℓ} (A : Type ℓ) (ℓ-rel : Level) : Type (ℓ ⊔ lsuc ℓ-rel) where
  no-eta-equality
  field Pathᵉ : A → A → Type ℓ-rel

open Extensional ⦃ ... ⦄ renaming (Pathᵉ to _∼_)
open Extensional

module _ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : X → Type ℓ'} {Z : (x : X) → Y x → Type ℓ''} where
  curry : ((p : Σ X Y) → Z (p .fst) (p .snd)) → (x : X) → (y : Y x) → Z x y
  curry f a b = f (a , b)

instance
  Extensional-default : ∀ {ℓ} {A} → Extensional {ℓ} A ℓ
  Extensional-default .Pathᵉ = _≡_
  {-# INCOHERENT Extensional-default #-}

  Extensional-Π
    : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : A → Type ℓ'}
    → ⦃ sb : ∀ {x} → Extensional (B x) ℓr ⦄
    → Extensional ((x : A) → B x) (ℓ ⊔ ℓr)
  Extensional-Π ⦃ sb ⦄ .Pathᵉ f g = ∀ x → Pathᵉ sb (f x) (g x)

  Extensional-uncurry
    : ∀ {ℓ ℓ' ℓ'' ℓr} {A : Type ℓ} {B : A → Type ℓ'} {C : Type ℓ''}
    → ⦃ sb : Extensional ((x : A) → B x → C) ℓr ⦄
    → Extensional (Σ A B → C) ℓr
  Extensional-uncurry ⦃ sb ⦄ .Pathᵉ f g = sb .Pathᵉ (curry f) (curry g)
  {-# OVERLAPPING Extensional-uncurry #-}

-- The Extensional-default is neither more or less specific than any of
-- the others (the level of the relation being fixed to the level of the
-- type prevents it from being a specialisation).
-- But we still want it to be discarded if there's some other instance.
-- That's what INCOHERENT is for.

module _ {A B : Type} where
  _ : {f g : (Σ A λ _ → A) → B} → (f ∼ g) ≡ ((x y : A) → f (x , y) ≡ g (x , y))
  _ = refl

  _ : {f g : A → B} → (f ∼ g) ≡ ((x : A) → f x ≡ g x)
  _ = refl
