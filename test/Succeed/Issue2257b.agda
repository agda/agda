-- Andreas, 2016-10-14, issue #2257, reported by m0davis
-- Bisected by Nisse.

{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS -v impossible:70 #-}

-- {-# OPTIONS -v tc.ip:20 #-}
-- {-# OPTIONS -v tc:20 #-}

record R (A : Set) : Set₁ where
  field
    a : A
    F : ∀ {f} → Set

  foo : Set
  foo = ∀ {f} → {!!}

  field
    bar : Set
