-- Andreas, 2021-07-25, issue #5478 reported by mrohman

{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS -v impossible:70 #-}
-- {-# OPTIONS -v tc:20 #-}
-- {-# OPTIONS -v tc.interaction:30 #-}
-- {-# OPTIONS -v tc.meta:25 #-}
-- {-# OPTIONS -v tc.rec:20 #-}
-- {-# OPTIONS -v tc.cc:25 #-}
-- {-# OPTIONS -v tc.record.eta.contract:20 #-}

record ⊤ : Set where

record R (A : Set) : Set₁ where
  foo : ⊤
  foo = {!!} -- works with _ instead of ?
  field
    X : Set
