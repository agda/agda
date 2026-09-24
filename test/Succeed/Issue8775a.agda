-- Andreas, 2026-09-24
-- Guard against a regression in the occurs checker encountered during work on #8775.

{-# OPTIONS --polarity #-}

module Issue8775a where

open import Agda.Builtin.Sigma

Ok : Set₁
Ok = Σ ((@- A : Set) → A) λ (_ : (@- A : Set) → A) → Set

Ok1 : Set₁
Ok1 = Σ ((@- A : Set) → A) λ _ → Set

Fails : Set₁
Fails = Σ _ λ (_ : (@- A : Set) → A) → Set
       -- ^ In an intermediate state while fixing #8775, Agda refused to solve this meta.
       -- Should be solved (see `Ok`).

-- Claude's elaboration:
--
-- `(@- A : Set) → A` is well-resourced: the codomain of a Pi is a type
-- position, and `workOnTypes` divides the context by `UnusedPolarity` there,
-- so the negative binder may be used.
--
-- Hence it must also be accepted as the solution of the metavariable in
-- `Fails` below, just as when it is supplied by hand in `Ok`.
