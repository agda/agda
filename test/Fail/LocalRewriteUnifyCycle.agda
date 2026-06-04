{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module _ (f : Nat → Nat → Nat) (n m : Nat) (@rewrite p : n ≡ 0) where
  foo : f n m ≡ m → Nat
  foo refl = 0

{-
Was:

> An internal error has occurred. Please report this as a bug.
> Location of the error: __IMPOSSIBLE_VERBOSE__, called at
> src/full/Agda/TypeChecking/Monad/Context.hs:783:9 in
> Agda-2.9.0-inplace:Agda.TypeChecking.Monad.Context

Now:

> LocalRewriteUnifyCycle.agda:9.7-11: error: [SplitError.UnificationStuck]
> I'm not sure if there should be a case for the constructor refl,
> because I get stuck when trying to solve the following unification
> problems (inferred index ≟ expected index):
>   f n m ≟ m
> Possible reason why unification failed:
>   Cannot solve variable m of type Nat with solution f 0 m because the
>   variable occurs in the solution, or in the type of one of the
>   variables in the solution.
> when checking that the pattern refl has type f n m ≡ m
-}
