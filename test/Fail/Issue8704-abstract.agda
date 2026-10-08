{-# OPTIONS --safe --without-K #-}

-- Issue #8704: The issue was that non-abstract metavariables could be solved
-- while checking an abstract definition. This could lead to both solutions that
-- are ill-typed and solutions that are non-unique (when viewed from outside the
-- abstract block).

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

-- Example 1: non-unique solution

mutual
  -- `secret` is definitionally equal to `false`, but only inside abstract
  -- blocks.
  abstract
    secret : Bool
    secret = false

  -- the meta `_` could be solved with either `secret` or `false`, which are not
  -- equal since `Test` is not abstract.
  Test : Set
  Test = secret ≡ _

  -- if we allow instantiating non-abstract metas while checking abstract
  -- definitions, then `test` below instantiates the meta with `secret`, which
  -- is unique in the context of `test` but non-unique in the original context
  -- of the meta.
  abstract
    test : Test
    test = refl

-- Example 2: ill-typed solution

mutual
  abstract
    hh : Bool
    hh = true

  -- writing `vv = refl` is rejected since `vv` is not abstract and hence cannot
  -- see the definition of `hh`.
  vv : hh ≡ true
  vv = _ -- refl

  -- however, if we allow instantiating non-abstract metas while checking
  -- abstract definitions, we can force the meta to be instantiated with the
  -- solution `refl`, which is well-typed in the context of `solve` but
  -- ill-typed in the original context of the meta.
  abstract
    Solve : Set
    Solve = vv ≡ refl

    solve : Solve
    solve = refl

