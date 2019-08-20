-- Andreas, 2019-08-20, issue #4012
-- unquoteDef and unquoteDecl should respect `private`

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

open M

test = g

-- Expect failure.
-- g is private in M, thus, should not be in scope
