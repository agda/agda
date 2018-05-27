-- Andreas, 2012-05-04 Example from Jason Reed, LFMTP 2009

-- Andreas, 2013-02-18 occurs check does not longer give error, hence
-- we only get unsolved metas.
{-
{-# OPTIONS --allow-unsolved-metas #-}
-- The option is supplied to force a real error to pass the regression test.
-}
module JasonReedPruning where

open import Common.Equality
open import Common.Product

data o : Set where
  f : o -> o

test :
  let U : o → o
      U = _
      V : o → o
      V = _
      W : o → o
      W = _
  in (x y : o) → U x ≡ f (V (W y))
               × V x ≡ U (W y)
test x y = refl , refl
{-
  Considering  U (W y) = V x, we can prune x from V

    V x = V'

  After instantiation

    U x = f V'       (solved)
    V'  = U (W y)    (not solved)

    U  = \ x → f V'
    V' = f V'
    occurs check fails
-}
