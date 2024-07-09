{-# OPTIONS --no-keep-pattern-variables #-}

open import Agda.Builtin.Equality

module _ (F : Set₁ → Set₁) where

  f : (B : Set₁) → B ≡ F Set → Set
  f B eq = {!eq!}

-- WAS: splitting on eq produces
--   f .(_ Set) refl = {!!}
-- with unsolved metavariables

-- SHOULD: instead produce
--   f .(F Set) refl = {!!}
