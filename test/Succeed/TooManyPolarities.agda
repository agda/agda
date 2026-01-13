-- Andreas, 2025-05-03, turn TooManyPolarities from error into warning

open import Agda.Builtin.Equality

------------------------------------------------------------------------
-- A clear case.
-- (Error is justifiable.)

postulate
  A : Set

{-# POLARITY A ++ #-}

-- warning: -W[no]TooManyPolarities
-- 1 too many polarities given in the POLARITY pragma for A

------------------------------------------------------------------------
-- Too eager warning.
-- (An error would be wrong here.)

interleaved mutual

  Sort : Set₁
  Sort = _

  postulate
    F : Sort

  {-# POLARITY F ++ #-}

  _ : Sort ≡ (Set → Set)
  _ = refl

-- We get this warning because postponing the check would be an overkill:

-- warning: -W[no]TooManyPolarities
-- 1 too many polarities given in the POLARITY pragma for F
