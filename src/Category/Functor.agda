------------------------------------------------------------------------
-- The Agda standard library
--
-- Functors
------------------------------------------------------------------------

-- Note that currently the functor laws are not included here.

module Category.Functor where

open import Function
open import Level

open import Relation.Binary.PropositionalEquality

record RawFunctor {ℓ} (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
  infixl 4 _<$>_ _<$_

  field
    _<$>_ : ∀ {A B} → (A → B) → F A → F B

  _<$_ : ∀ {A B} → A → F B → F A
  x <$ y = const x <$> y

-- A functor morphism from F₁ to F₂ is an operation op such that
-- op (F₁ f x) ≡ F₂ f (op x)

record Morphism {ℓ} {F₁ F₂ : Set ℓ → Set ℓ}
                (fun₁ : RawFunctor F₁)
                (fun₂ : RawFunctor F₂) : Set (suc ℓ) where
  open RawFunctor
  field
    op     : ∀{X} → F₁ X → F₂ X
    op-<$> : ∀{X Y} (f : X → Y) (x : F₁ X) →
             op (fun₁ ._<$>_ f x) ≡ fun₂ ._<$>_ f (op x)
