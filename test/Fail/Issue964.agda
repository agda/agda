-- Andreas, 2016-08-04, issue #964
-- Allow open metas and interaction points in imported files

-- {-# OPTIONS -v import:100 #-}
-- {-# OPTIONS -v meta.postulate:20 #-}
-- {-# OPTIONS -v tc.conv.level:50 #-}

open import Common.Level
open import Common.Equality

postulate something : Set₁

open import Common.Issue964.UnsolvedMetas something

test =  M.N.meta3

shouldFail : _≡_ {A = Level} meta (lsuc (lsuc lzero))
shouldFail = refl

-- WAS: WEIRD ERROR:
-- Set (Set .Issue964.UnsolvedMetas.1) != Set₂
-- when checking that the expression refl has type
-- meta ≡ lsuc (lsuc lzero)

-- NOW:
-- Set (.Issue964.UnsolvedMetas.unsolved#meta.1 something) != Set₂
-- when checking that the expression refl has type
-- meta ≡ lsuc (lsuc lzero)
