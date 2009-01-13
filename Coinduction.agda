------------------------------------------------------------------------
-- Type used to make recursive arguments coinductive
------------------------------------------------------------------------

-- See Data.Colist for examples of how this type is used, or
-- http://article.gmane.org/gmane.comp.lang.agda/633 for a longer
-- explanation.

module Coinduction where

-- If you never pattern match on ♯_, and never use ~ except right
-- before ♯_, then you can avoid a problem which causes subject
-- reduction to fail.

infix 10 ♯_

codata ∞ (T : Set) : Set where
  ♯_ : (x : T) → ∞ T

♭ : ∀ {T} → ∞ T → T
♭ (♯ x) = x

-- Variant for Set1.

codata ∞₁ (T : Set1) : Set1 where
  ♯_ : (x : T) → ∞₁ T

♭₁ : ∀ {T} → ∞₁ T → T
♭₁ (♯ x) = x
