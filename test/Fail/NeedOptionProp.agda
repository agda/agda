-- Andreas, 2024-07-19, PR #7379
-- Trigger error NeedOptionProp

{-# OPTIONS --no-prop #-}

open import Agda.Primitive

postulate
  A : Prop

-- Expected error:
-- Universe Prop is disabled (use options --prop and --no-prop to enable/disable Prop)
