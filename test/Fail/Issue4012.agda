-- Andreas, 2019-08-20, issue #4012
-- unquoteDef and unquoteDecl should also work in abstract blocks.

open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.List
open import Agda.Builtin.Equality

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

test : f ≡ g
test = refl

-- Expected error:

-- f !=< g of type D
-- when checking that the expression refl has type f ≡ g
