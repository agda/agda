------------------------------------------------------------------------
-- Applicative functors
------------------------------------------------------------------------

-- Note that currently the applicative functor laws are not included
-- here.

module Category.Applicative where

open import Data.Unit
open import Category.Applicative.Indexed

RawApplicative : (Set → Set) → Set₁
RawApplicative F = RawIApplicative {I = ⊤} (λ _ _ → F)

module RawApplicative {F : Set → Set} (app : RawApplicative F) where
  open RawIApplicative app public
