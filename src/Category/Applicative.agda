------------------------------------------------------------------------
-- The Agda standard library
--
-- Applicative functors
------------------------------------------------------------------------

-- Note that currently the applicative functor laws are not included
-- here.

module Category.Applicative where

open import Data.Unit
open import Category.Applicative.Indexed

RawApplicative : ∀ {f} → (Set f → Set f) → Set _
RawApplicative F = RawIApplicative {I = ⊤} (λ _ _ → F)

module RawApplicative {f} {F : Set f → Set f}
                      (app : RawApplicative F) where
  open RawIApplicative app public
