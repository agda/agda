------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed applicative functors
------------------------------------------------------------------------

-- Note that currently the applicative functor laws are not included
-- here.

module Category.Applicative.Indexed where

open import Category.Functor using (RawFunctor)
open import Data.Product
open import Function
open import Level
open import Relation.Binary.PropositionalEquality as P using (_≡_)

IFun : ∀ {i} → Set i → (ℓ : Level) → Set _
IFun I ℓ = I → I → Set ℓ → Set ℓ

record RawIApplicative {i f} {I : Set i} (F : IFun I f) :
                       Set (i ⊔ suc f) where
  infixl 4 _⊛_ _<⊛_ _⊛>_
  infix  4 _⊗_

  field
    pure : ∀ {i A} → A → F i i A
    _⊛_  : ∀ {i j k A B} → F i j (A → B) → F j k A → F i k B

  rawFunctor : ∀ {i j} → RawFunctor (F i j)
  rawFunctor = record
    { _<$>_ = λ g x → pure g ⊛ x
    }

  private
    open module RF {i j : I} =
           RawFunctor (rawFunctor {i = i} {j = j})
           public

  _<⊛_ : ∀ {i j k A B} → F i j A → F j k B → F i k A
  x <⊛ y = const <$> x ⊛ y

  _⊛>_ : ∀ {i j k A B} → F i j A → F j k B → F i k B
  x ⊛> y = flip const <$> x ⊛ y

  _⊗_ : ∀ {i j k A B} → F i j A → F j k B → F i k (A × B)
  x ⊗ y = (_,_) <$> x ⊛ y

  zipWith : ∀ {i j k A B C} → (A → B → C) → F i j A → F j k B → F i k C
  zipWith f x y = f <$> x ⊛ y

-- Applicative functor morphisms, specialised to propositional
-- equality.

record Morphism {i f} {I : Set i} {F₁ F₂ : IFun I f}
                (A₁ : RawIApplicative F₁)
                (A₂ : RawIApplicative F₂) : Set (i ⊔ suc f) where
  module A₁ = RawIApplicative A₁
  module A₂ = RawIApplicative A₂
  field
    op      : ∀ {i j X} → F₁ i j X → F₂ i j X
    op-pure : ∀ {i X} (x : X) → op (A₁.pure {i = i} x) ≡ A₂.pure x
    op-⊛    : ∀ {i j k X Y} (f : F₁ i j (X → Y)) (x : F₁ j k X) →
              op (f A₁.⊛ x) ≡ (op f A₂.⊛ op x)

  op-<$> : ∀ {i j X Y} (f : X → Y) (x : F₁ i j X) →
           op (f A₁.<$> x) ≡ (f A₂.<$> op x)
  op-<$> f x = begin
    op (A₁._⊛_ (A₁.pure f) x)       ≡⟨ op-⊛ _ _ ⟩
    A₂._⊛_ (op (A₁.pure f)) (op x)  ≡⟨ P.cong₂ A₂._⊛_ (op-pure _) P.refl ⟩
    A₂._⊛_ (A₂.pure f) (op x)       ∎
    where open P.≡-Reasoning
