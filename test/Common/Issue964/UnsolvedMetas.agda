
-- Andreas, 2016-08-04, issue #964
-- Allow open metas and interaction points in imported files

{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS -v import:100 #-}
-- {-# OPTIONS -v meta.postulate:20 #-}
-- {-# OPTIONS -v tc.meta:25 #-}

open import Common.Level

module Common.Issue964.UnsolvedMetas (A : Set₁) where

meta : Level
meta = {!!}  -- unsolved interaction point

module M (B : Set) where

  meta2 : Set meta
  meta2 = _  -- unsolved meta

  module N (C D : meta2) where

    meta3 : meta2
    meta3 = Set

-- EOF
