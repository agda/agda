module ConstructorHeadedDivergenceIn2-2-10 where

data ⊤ : Set where
  tt : ⊤

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

{- Brandon Moore reports (July 2011)
In 2.2.10 the following code seems to cause typechecking
to diverge.
-}

f : ℕ → Set
f zero = ⊤
f (suc n) = ℕ × f n

enum : (n : ℕ) → f n
enum zero = tt
enum (suc n) = n , enum n

n : ℕ
n = _

test : f n
test = enum (suc n)
{-
This typechecks quickly if the definition
of test is changed to

test = enum n

I think the problem is that the body has type ℕ × f n,
and unifying it with the expected type f n invokes the
constructor-headed function specialization to resolve
n to suc n', and the process repeats.

Brandon
-}

-- Andreas, 2011-07-28 This bug is not reproducible in the darcs
-- version.
--
-- This file should fail with unresolved metas.