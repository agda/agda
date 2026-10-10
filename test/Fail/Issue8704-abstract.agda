{-# OPTIONS --safe --without-K #-}

-- Issue #8704: The issue was that non-abstract metavariables could be solved
-- while checking an abstract definition. This could lead to solutions that
-- are ill-typed (when viewed from outside the abstract block).
--
-- Solutions that are non-unique when viewed from outside the abstract block
-- are still accepted, see test/Succeed/Issue8704-non-unique.agda.

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

-- Ill-typed solution

mutual
  abstract
    hh : Bool
    hh = true

  -- writing `vv = refl` is rejected since `vv` is not abstract and hence cannot
  -- see the definition of `hh`.
  vv : hh ≡ true
  vv = _ -- refl

  -- however, if we allowed instantiating non-abstract metas while checking
  -- abstract definitions without rechecking the solution, we could force the
  -- meta to be instantiated with the solution `refl`, which is well-typed in
  -- the context of `solve` but ill-typed in the original context of the meta.
  abstract
    Solve : Set
    Solve = vv ≡ refl

    solve : Solve
    solve = refl


-- Variant: the solution of a non-abstract meta must not mention unsolved
-- abstract metas, since these could later be instantiated with a solution
-- that is ill-typed in the original context of the non-abstract meta.

mutual
  abstract
    hh' : Bool
    hh' = true

    ww : hh' ≡ true
    ww = _

  vv' : hh' ≡ true
  vv' = _

  abstract
    -- We should not solve the meta of vv' with the meta of ww ...
    Solve' : Set
    Solve' = vv' ≡ ww

    solve' : Solve'
    solve' = refl

    -- ... since the latter can then be solved by refl.
    Solve'' : Set
    Solve'' = ww ≡ refl

    solve'' : Solve''
    solve'' = refl
