-- Andreas, 2012-05-24, issue reported by Nisse
{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS -v tc.meta:50 #-}
module Issue658 where

import Common.Level

postulate
  A : Set
  P : A → Set
  Q : (x : A) → P x → Set
  p : (x : A) → P x

record R : Set where
  field
    a : A

r : R
r = {!!}

postulate
  q : Q (R.a r) (p (R.a r))

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/MetaVars.hs:101

-- The internal error was cause by eta-expanding the frozen meta.
-- Eta-expansion of frozen metas is now allowed.
