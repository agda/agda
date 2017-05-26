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
