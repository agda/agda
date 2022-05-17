-- Andreas, Ulf, 2022-05-06, AIM XXXV
-- Make sure you cannot trick Agda into admitting data types in IUniv.
-- The previous check let this exploit through.
-- Note: I : IUniv : SSet₁

open import Agda.Primitive.Cubical

mutual
  Univ = _
  data False : Univ where

  I' : Univ
  I' = I

-- Should fail.

-- Error:
-- The universe _6 of False
-- is unresolved, thus does not permit data or record declarations
-- when checking the definition of False
