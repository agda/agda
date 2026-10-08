{-# OPTIONS --safe --without-K #-}

{- Issue #8704: a proof of false exploiting a bug with abstract.

If we allow solving non-abstract metas from inside an abstract block, then we
can create ill-typed terms. The example below exploits this through an
optimization in clause-based reduction to prove false.

-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data IsNat : Nat → Set where
  isZero : IsNat zero
  isSuc  : (n : Nat) → IsNat (suc n)


g : (n : Nat)      -- In the exploit, this argument will be abstract...
  → (v : IsNat n)  -- ...while this will be concrete.
  → Bool           -- This argument is purely technical so we can have a third clause.
  → Bool

-- This clause fires as soon as the second argument is a `isSuc`.
g .(suc _) (isSuc _) _ = true

-- The following catchall clause could be g _ _ _ = false
-- if not for the need of a third clause
-- that exploits the clause-based reducer for the first two clauses.
{-# CATCHALL #-}
g n v true  = false
-- We need the first two clauses in scope but not yet translated to case-trees.
-- So we have a third clause with a local module that is checked
-- using clause-based reduction for the first two-clauses.
g n v false = false
  module Leak where
    -- The code below instantiates `leak = mk (isSuc zero)`, which is ill-typed
    -- since it relies on `secret` being equal to `suc zero`.
    abstract
      secret : Nat
      secret = suc zero
    leak : IsNat secret
    leak = _
    data MkLeak : IsNat secret → Set where
      mk : (w : IsNat secret) → MkLeak w
    abstract
      solve : MkLeak leak
      solve = mk (isSuc zero)
    -- Inside the abstract block, `secret` reduces to `suc zero` and hence
    -- `g secret leak true` matches the first clause and evaluates to `true`.
    abstract
      lemma : g secret leak true ≡ true
      lemma = refl
    -- Outside the abstract block, `secret` does not reduce.
    -- Due to PR #7211 before the fix in PR #8821: Clause-based reduction
    -- of `g` assumes that if `n` is not a successor, then `v` cannot be a `isSuc`
    -- either. Hence it skips to the next clause and returns `false`.
    false≡true : false ≡ true
    false≡true = lemma

data ⊥ : Set where

false≢true : false ≡ true → ⊥
false≢true ()

absurd : ⊥
absurd = false≢true (Leak.false≡true zero isZero)
