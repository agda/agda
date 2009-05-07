------------------------------------------------------------------------
-- Types used to make recursive arguments coinductive
------------------------------------------------------------------------

-- See Data.Colist for examples of how this type is used, or
-- http://article.gmane.org/gmane.comp.lang.agda/633 for a longer
-- explanation.

module Coinduction where

infix 10 ♯_ ♯₁_

codata ∞ (T : Set) : Set where
  ♯_ : (x : T) → ∞ T

♭ : ∀ {T} → ∞ T → T
♭ (♯ x) = x

-- Variant for Set₁.

codata ∞₁ (T : Set₁) : Set₁ where
  ♯₁_ : (x : T) → ∞₁ T

♭₁ : ∀ {T} → ∞₁ T → T
♭₁ (♯₁ x) = x
