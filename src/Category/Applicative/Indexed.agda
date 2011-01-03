------------------------------------------------------------------------
-- Indexed applicative functors
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- Note that currently the applicative functor laws are not included
-- here.

module Category.Applicative.Indexed where

open import Category.Functor
open import Data.Product
open import Function
open import Level

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
