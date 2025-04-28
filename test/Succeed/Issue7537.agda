-- Andreas, 2025-04-28, issue #7537, reported by Liang-Ting Chen
-- Test case by Szumi Xie

{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Cubical.Path

data T : Set where
  e : T
  p : (x : T) → e ≡ x
  q : e ≡ e

f : T → T
f e = {!!}
f x = {!!}

-- Used to diverge.
-- Should succeed with unsolved metas.
