
-- Andreas, 2019-08-20, issue #4016

-- Debug printing should not crash Agda even if there are
-- __IMPOSSIBLE__s buried inside values that get printed.

{-# OPTIONS -v scope.decl.trace:80 #-}  -- KEEP!

-- The following is some random code (see issue #4010)
-- that happened to trigger an internal error with verbosity 80.

open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.List

data D : Set where
  c : D

module M where

  private

    unquoteDecl g = do
      ty ← quoteTC D
      _  ← declareDef (arg (arg-info visible relevant) g) ty
      qc ← quoteTC c
      defineFun g (clause [] qc ∷ [])

-- Should print lots of debug stuff and succeed.
