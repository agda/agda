-- Issue #2814 reported by tomjack on 2017-10-18

{-# OPTIONS --cubical --rewriting --confluence-check #-}

-- prelude stolen from Saizan/cubical-demo

open import Agda.Primitive.Cubical public

postulate
  Path' : ∀ {ℓ} {A :     Set ℓ} → A    → A    → Set ℓ
  PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

{-# BUILTIN PATHP        PathP     #-}

infix 4 _≡_
_≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_≡_ {A = A} = PathP (λ _ → A)

Path = _≡_

refl : ∀ {ℓ} {A : Set ℓ} {x : A} → x ≡ x
refl {x = x} = λ _ → x

postulate
  Rewrite : ∀ {ℓ} {A : Set ℓ} → A → A → Set

{-# BUILTIN REWRITE Rewrite #-}



module Good where
  postulate
    Unit : Set
    unit : Unit

  module UnitElim (P : Unit → Set) (unit* : P unit) where
    postulate
      Unit-elim : (x : Unit) → P x
      unit-β : Rewrite (Unit-elim unit) unit*
  open UnitElim public
  {-# REWRITE unit-β #-}

  test₁ : {C : Set} {c₀ : C} → Path {A = C} (Unit-elim (λ _ → C) c₀ unit) c₀
  test₁ = refl

  test₂ : {C : Set} {c₀ : C} → Path {A = Path c₀ c₀} (λ j → Unit-elim (λ _ → C) c₀ unit) refl
  test₂ = refl


-- same code, but with a dummy module parameter
module Bad (Dummy : Set) where
  postulate
    Unit : Set
    unit : Unit

  module UnitElim (P : Unit → Set) (unit* : P unit) where
    postulate
      Unit-elim : (x : Unit) → P x
      unit-β : Rewrite (Unit-elim unit) unit*
  open UnitElim public
  {-# REWRITE unit-β #-}

  test₁ : {C : Set} {c₀ : C} → Path {A = C} (Unit-elim (λ _ → C) c₀ unit) c₀
  test₁ = refl
  test₂ : {C : Set} {c₀ : C} → Path {A = Path c₀ c₀} (λ j → Unit-elim (λ _ → C) c₀ unit) refl
  test₂ = refl


-- WAS:
-- Unit-elim (λ _ → .C) .c₀ unit != .c₀ of type .C
-- when checking that the expression refl has type
-- Path (λ j → Unit-elim (λ _ → .C) .c₀ unit) refl

-- SHOULD: succeed
