-- Andreas, 2026-09-03, issue #8532, reported by WhatisRT,
-- minimized by szumixie.
--
-- Variant of Issue8532.agda that exercises the ordinary reduction machinery.
--
-- The projection @M.G.β@ was applied to a value whose type was headed by
-- @H._.G@, a copy of @M.G@ stemming from the module application @open M ℕ@.
-- Taking the "parameters" of the projection from the arguments of the copy
-- produced the ill-typed type @F.X x@ (with @x : H ℕ@ a record value),
-- which crashed the (fast) reduction machinery.
--
-- The unsolved metas are not essential to the issue,
-- they just could not be avoided when minimizing it.

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-fast-reduce #-}

module Issue8532NoFast where

open import Agda.Builtin.Equality

postulate
  ℕ : Set

record F : Set₁ where
  field
    X : Set

postulate
  fun : (P : Set) → P
  xx : F

module M (_ : Set) where
  record G (m : F) : Set where
    field
      α : (i : ℕ) → _ → ℕ
      β : F.X m → ℕ

record H (_ : Set) : Set where
  open M ℕ

  f : ℕ → ℕ
  f _ = G.α (fun (G xx)) (G.β (fun (G xx)) _) _

x : H ℕ
x = record {}

pf : H.f x _ ≡ H.f x _
pf = refl

-- WAS: internal error in Agda.TypeChecking.Reduce.Fast (fast reduction)
-- resp. Agda.TypeChecking.Substitute (@conApp@, ordinary reduction).
-- Should succeed (modulo unsolved metas).
