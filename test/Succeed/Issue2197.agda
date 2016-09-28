-- Andreas, 2016-09-20, issue #2197 reported by m0davis

{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS -v tc.pos:20 -v tc.meta.eta:20 #-}

record R : Set where
  inductive

  field
    foo : R

  bar : R
  bar = {!!}

-- This used to loop due to infinite eta-expansion.
-- Should check now.
