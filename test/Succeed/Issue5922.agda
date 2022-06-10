-- Andreas, 2022-06-10, issue #5922, reported by j-towns.
-- Lack of normalization of data projections against data constructors
-- breaks termination checker applied to extended lambda gone through
-- forcing translation and reflection.

-- The workaround was to turn off the forcing translation:
-- {-# OPTIONS --no-forcing #-}

-- {-# OPTIONS -v term:20 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

data Fin : Nat → Set where
  fz : (b : Nat)         → Fin (suc b)
  fs : (b : Nat) → Fin b → Fin (suc b)

apply : {A B C : Set} (input : A) (f : A → B) (cont : B → C) → C
apply input f cont = cont (f input)

macro
  id-macro : (b : Nat) → (Fin b → Nat) → Term → TC ⊤
  id-macro b f hole =
    bindTC (quoteTC f) λ f-term →
    unify hole f-term

test : (b : Nat) → Fin b → Nat
test b = id-macro b λ where
  (fz _)   → zero
  (fs a x) → apply x (test a) suc

-- Should termination check.

-- WAS:
-- Termination checking failed for the following functions:
--   test
-- Problematic calls:
--   λ { (fz .(Agda.Builtin.Nat.suc-0 _)) → zero
--     ; (fs .(Agda.Builtin.Nat.suc-0 _) x)
--         → apply x
--           (test (Agda.Builtin.Nat.suc-0 (suc (Agda.Builtin.Nat.suc-0 b))))
--           suc
--     }
--   test (Agda.Builtin.Nat.suc-0 (suc b))
--
-- This shows data projection Agda.Builtin.Nat.suc-0 applied to data constructor
-- suc, which should be normalized away.
