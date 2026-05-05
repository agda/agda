-- Andreas, 2026-05-05, issue #4228
-- Solved interaction points should not depend on genTel after generalization.

-- {-# OPTIONS -v tc.generalize:30 #-}

postulate
  F : Set → Set
  P : (A : Set) → F A → Set
  f : (A : Set) → F A

variable
  A : Set

postulate
  p : P {!!} (f A)   -- C-c C-,

-- WAS:
-- Goal: Set
-- ————————————————————————————————————————————————————————————
-- genTel : Issue3656.GeneralizeTel   (not in scope)

-- NOW:
-- Goal: Set
-- ———— Context ———————————————————————————————————————————————
-- A : Set
