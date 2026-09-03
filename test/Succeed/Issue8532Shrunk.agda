-- Andreas, 2026-09-03, issue #8532.
-- Further shrunk by Claude, but with essential idea from Szumi Xie.
--
-- Essential ingredients:
--   * a parameterized module M containing a parameterized record G,
--   * a module application (here: @open M ℕ@) inside a *parameterized*
--     record H, creating a copy @H._.G@ of @G@ whose leading arguments
--     are the parameters of H rather than those of G,
--   * a projection (@β@) whose type mentions G's parameter @m@,
--   * a record value (@record {}@) instantiating H's record variable.
--
-- The unsolved metas are not essential to the issue.

{-# OPTIONS --allow-unsolved-metas #-}

module Issue8532Shrunk where

open import Agda.Builtin.Equality

postulate ℕ : Set

record F : Set₁ where
  field X : Set

postulate xx : F

module M (_ : Set) where
  record G (m : F) : Set where
    field
      α : (i : ℕ) → _ → ℕ
      β : F.X m → ℕ

record H (_ : Set) : Set where
  open M ℕ
  postulate g : G xx

  f : ℕ → ℕ
  f _ = G.α g (G.β g _) _

x : H ℕ
x = record {}

pf : H.f x _ ≡ H.f x _
pf = refl

-- WAS: internal error in Agda.TypeChecking.Reduce.Fast,
-- because @G.β g@ was assigned the ill-typed type @F.X x → ℕ@.
-- Should succeed (modulo unsolved metas).
