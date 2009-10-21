------------------------------------------------------------------------
-- Types used to make recursive arguments coinductive
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- See Data.Colist for examples of how this type is used, or
-- http://article.gmane.org/gmane.comp.lang.agda/633 for a longer
-- explanation.

module Coinduction where

open import Level

infix 10 ♯_

codata ∞ {ℓ} (T : Set ℓ) : Set ℓ where
  ♯_ : (x : T) → ∞ T

♭ : ∀ {ℓ} {T : Set ℓ} → ∞ T → T
♭ (♯ x) = x
