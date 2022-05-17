-- Andreas, 2021-01-28 documenting #4702, reported by gallais

open import Agda.Builtin.Nat

case_of_ : {A B : Set} → A → (A → B) → B
case x of f = f x

-- Needed for making `plus` pass the termination checker.
-- Used to be automatic via `--auto-inline`, since 2.6.2 this flag
-- is off by default.

{-# INLINE case_of_ #-}

plus : Nat → Nat → Nat
plus m n = case m of λ
   { zero    → n
   ; (suc m) → suc (plus m n)
   }
