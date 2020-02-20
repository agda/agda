{-# OPTIONS  --sized-types --show-implicit #-}

module SizedTypesScopeViolationInMeta where

open import Agda.Builtin.Size

data Nat : {size : Size} -> Set where
  zero : {size : Size} -> Nat {↑ size}
  suc  : {size : Size} -> Nat {size} -> Nat {↑ size}

-- exposing a bug in size constraint solving

-- *** Exception: Inconsistent meta: _73 [[CtxId 420],[CtxId 418]]
A : Set1
A = (Id : {i : Size} -> Nat {_} -> Set)
    (k : Size)(m : Nat {↑ k}) -> Id {k} m
    ->
    (j : Size)(n : Nat {j}) -> Id {j} n

-- Current error (problematic):
--
-- Cannot solve size constraints
-- [Id, k, m, j, n] j ≤ (_size_9 (i = j))
-- [Id, k, m, j, n] (↑ k) ≤ (_size_9 (i = k))
-- Reason: inconsistent lower bound for 9
-- when checking that the expression n has type Nat {_size_9 {i = j}}

{-
mutual

--   id : {i : Size} -> Nat {_} -> Nat {i}  -- FAILS
  id : {i : Size} -> Nat {i} -> Nat {i}
  id x = x

  succ : {i : Size} -> Nat {i} -> Nat {↑ i}
  succ x = suc (id x)
-}
