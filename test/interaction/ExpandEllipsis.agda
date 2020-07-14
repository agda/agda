-- Andreas, 2017-05-26
-- Expand ellipsis with C-c C-c . RET

open import Agda.Builtin.Nat

test0 : Nat → Nat
test0 x with zero

... | q = {!.!}  -- C-c C-c

-- Expected result:
-- test0 x | q = ?

data Fin : Nat → Set where
  zero : ∀ n → Fin (suc n)
  suc  : ∀{n} → Fin n → Fin (suc n)

test1 : ∀{n} → Fin n → Nat

test1 (zero _) with Nat

... | q = {!.!} -- C-c C-c

-- Expected result:
-- test1 (zero _) | q = ?

test1 {.(suc n)} (suc {n} i) with Fin zero

... | q = {!.!} -- C-c C-c

-- Expected result:
-- test1 {.(suc n)} (suc {n} i) | q = ?

-- Since commit e531104 this test case is broken.
-- The ellipsis is not expanded literally (due to dot shuffling?).
-- https://github.com/agda/agda/commit/e531104ecdfd9efc1e76bf0e9b5f9690f31bcaab#r40133390
