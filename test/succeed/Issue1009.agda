-- 2013-12-28 Andreas, issue reported by Christian Sattler

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS -v tc.cc:15 #-} -- Keep! Debug printing triggered the problem.

record Σ (A : Set) (B : A → Set) : Set where
  field
    fst : A
    snd : B fst

test : {A : Set} → Σ A (λ {_ → A})
test = _

-- This used to trigger an internal error
-- (funnily only at -v tc.cc:15 verbosity)
-- because adding the clause to an
-- extended lambda failed.  Reason:
-- Extended lambda was registered as Axiom
-- during first checking, not Defn as
-- checkFunDef' now expects.
