-- Andreas, 2016-05-10, issue 1848, reported by Nisse

-- {-# OPTIONS -v tc.lhs.top:20 #-}

data D : Set where
  c : D → D

postulate
  P : D → Set

foo : (x : D) → P x
foo _ = {!!}

-- checked lhs:
--   ps    =  _
--   delta =  (x : D)
--   qs    =  [r(x = VarP (0,"x"))]

-- The unnamed variable is part of the context:

-- Goal: P .x
-- ————————————————————————————————————————————————————————————
-- .x : D

bar : (x : D) → P x
bar (c _) = {!!}

-- WAS:
-- checked lhs:
--   ps    =  _
--   delta =  (_ : D)
--   qs    =  [r(x = ConP Issue1848.D.c ... [r(_ = VarP (0,"_"))])]

-- The unnamed variable is not part of the context:

-- Goal: P (c _)
-- ————————————————————————————————————————————————————————————

-- This can, in more complicated situations, make the goal type harder
-- to understand.

-- NOW:
-- Unnamed variable should be displayed in the context, e.g., as ".x"
