module _ where

open import Agda.Builtin.List
open import Agda.Builtin.Reflection

macro

  easy : Term → TC _
  easy t =
    bindTC (freshName "A") λ A →
    bindTC (declarePostulate (arg (arg-info visible relevant) A)
                             (agda-sort (lit 0))) λ _ →
    unify (def A []) t

B : Set
B = {!easy!}

-- WAS:
-- Parse error
-- ;<ERROR>
-- Example.A...

-- SHOULD: complain that A is not in scope
