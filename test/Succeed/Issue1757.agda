-- Andreas, 2015-12-28, issue reported by effectfully
-- {-# OPTIONS -v tc.data.fits:15 -v tc.conv.sort:30 -v tc.conv.nat:30 #-}

open import Common.Level

postulate
  fun : Level → Level

data Test : Set (fun lzero) where
  c : Test → Test

-- The primitive lzero in argument of neutral is what matters here.
-- Agda reported:
--   The type of the constructor does not fit in the sort of the
--   datatype, since Set (fun lzero) is not less or equal than
--   Set (fun lzero)
-- Upon inspection of non-prettyTCM Terms, one side had turned
-- `lzero` into `Level (Max [])`, whereas it remained `Def lzero []`
-- on the other side.

-- Should work now.
