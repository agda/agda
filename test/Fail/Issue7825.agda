-- Andreas, 2025-04-29, issue #7825
-- DISPLAY forms for irrelevant projections should not drop parameters
-- as those are only absent in relevant projections.

{-# OPTIONS --irrelevant-projections #-}
{-# OPTIONS --show-irrelevant #-}

record Squash (A : Set) : Set where
  field .theSquashed : A

postulate
  IRRELEVANT : Set

{-# DISPLAY Squash.theSquashed _ = IRRELEVANT #-}

postulate
  P : {A : Set} → .A → Set

_ : P (λ r → Squash.theSquashed r)
_ = Set

-- expected error: [UnequalTerms]
-- Set₁ !=< P (λ r → IRRELEVANT)
-- when checking that the expression Set has type P (λ r → IRRELEVANT)
