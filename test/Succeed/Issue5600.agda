-- Issue #5600, reported 2021-10-14 by Samuel Mimram.
-- Dependency on cubical library removed by Nisse.
-- Issue fixed 2021-11-24 by Andrea in #5672.
-- Test added 2022-08-29 by Andreas.

{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat

refl : {A : Set₁} (x : A) → x ≡ x
refl x = λ _ → x

mutual

  data A : Set₁ where
    s : A → A
    e : {k : Nat} {n : A} → refl (f (suc zero) n) ≡ refl (s n)

  f : Nat → A → A
  f zero    n = n
  f (suc k) n = s (f k n)

-- Should succeed.
--
-- Error was:
-- s n != f 1 n of type A
-- when checking that the expression refl {x = s n} has type
-- f 1 n ≡ f 1 n
