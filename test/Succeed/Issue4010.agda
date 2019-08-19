-- Andreas, 2019-08-19, issue #4010
-- unquoteDef and unquoteDecl should also work in abstract blocks.

open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.List

abstract

  data D : Set where
    c : D

  f : D
  unquoteDef f = do
    qc ← quoteTC c  -- Previously, there was a complaint here about c.
    defineFun f (clause [] qc ∷ [])

  unquoteDecl g = do
    ty ← quoteTC D
    _  ← declareDef (arg (arg-info visible relevant) g) ty
    qc ← quoteTC c
    defineFun g (clause [] qc ∷ [])
