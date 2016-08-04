-- Andreas, 2016-08-04, issue #964
-- Allow open metas and interaction points in imported files

-- {-# OPTIONS -v import:100 #-}
-- {-# OPTIONS -v meta.postulate:20 #-}
-- {-# OPTIONS -v tc.conv.level:50 #-}

open import Common.Level
open import Common.Equality

postulate something : Set₁

open import Common.Issue964.UnsolvedMetas something

test1 : Level
test1 = meta

test2 : (B : Set) → Set test1
test2 B = M.meta2 B

test3 = M.N.meta3

-- Should succeed
