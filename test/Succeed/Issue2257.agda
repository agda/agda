-- Andreas, 2016-10-14, issue #2257, reported by m0davis
-- Bisected by Nisse.

{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS -v tc.ip:20 #-}
-- {-# OPTIONS -v tc:20 #-}


record R : Set₁ where
  foo : Set
  foo = ∀ {f} → {!!}

  field
    bar : Set
