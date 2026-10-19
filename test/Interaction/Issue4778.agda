{-# OPTIONS --no-keep-pattern-variables #-}

-- {-# OPTIONS -vtc.with.strip:60 -v tc.lhs.top:50 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

postulate
  trustMe : {A : Set} (x y : A) → x ≡ y

data Fin : Nat → Set where
  fzero : ∀ n → Fin (suc n)
  fsuc  : ∀{n} → Fin n → Fin (suc n)

test1 : ∀{n} → Fin n → Nat
test1 (fzero _) = 0
test1 {.(suc n)} (fsuc {n} i) with Fin zero
... | q = {!.!}
-- Current & expected expansion:
-- test1 {.(suc n)} (fsuc {n} i) | q = {!!}

test2 : ∀{n} → Fin n → Nat
test2 (fzero _) = 0
test2 {.(suc n)} (fsuc {n} i) with trustMe n zero
... | refl = {!.!}
-- Current & expected expansion:
-- test2 {.1} (fsuc {.0} i) | refl = {!!}

-- The test cases below do not yet work correctly, but are included
-- here as documentation of the current behaviour of Agda. does not
-- work correctly yet.

test3 : ∀{n} → Fin n → Nat
test3 (fzero _) = 0
test3 {m} (fsuc {n} i) with Fin zero
... | q = {!.!}
-- Current expansion:
-- test3 {.(suc _)} (fsuc {_} i) | q = {!!}
-- Expected expansion:
-- test3 {.(suc n)} (fsuc {n} i) | q = { }

test4 : ∀{n} → Fin n → Nat
test4 (fzero _) = 0
test4 {_} (fsuc {n} i) with Fin zero
... | q = {!.!}
-- Current expansion:
-- test4 {.(suc _)} (fsuc {_} i) | q = {!!}
-- Expected expansion:
-- test4 {_} (fsuc {n} i) | q = {!!}

test5 : ∀{n : Nat} → Fin n → Nat → Nat
test5 (fzero _) _ = 0
test5 {.(suc n)} (fsuc {n} i) m with trustMe m n
... | refl = {!.!}
-- Current expansion:
-- test5 {.(suc n)} (fsuc {n} i) n | refl = {!!}
-- Expected expansion: one of the following:
-- test5 {.(suc n)} (fsuc {n} i) .n | refl = {!!}
-- test5 {.(suc m)} (fsuc {.m} i) m | refl = {!!}

test6 : Nat → ∀{n : Nat} → Fin n → Nat
test6 _ (fzero _) = 0
test6 m {.(suc n)} (fsuc {n} i) with trustMe m n
... | refl = {!.!}
-- Current expansion:
-- test6 m {.(suc m)} (fsuc {.m} i) | refl = {!!}
-- This one is actually good, we should be sure fixing the above
-- examples doesn't change the output here!
