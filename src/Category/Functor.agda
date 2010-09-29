------------------------------------------------------------------------
-- Functors
------------------------------------------------------------------------

-- Note that currently the functor laws are not included here.

{-# OPTIONS --universe-polymorphism #-}
module Category.Functor where

open import Function
open import Level

record RawFunctor {ℓ} (f : Set ℓ → Set ℓ) : Set (suc ℓ) where
  infixl 4 _<$>_ _<$_

  field
    _<$>_ : ∀ {a b} → (a → b) → f a → f b

  _<$_ : ∀ {a b} → a → f b → f a
  x <$ y = const x <$> y
