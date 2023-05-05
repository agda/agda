-- Andreas, 2022-08-31, issue #6059, raised by Nisse in code review.
-- Test case by Andreas and Nisse.

-- The termination checker asserted `c (suc n) _ > c n` when comparing
-- pattern `c (suc n) _` to call argument `c n`.
-- This is unsound, and can be exploited to proof absurdity.

{-# OPTIONS --termination-depth=2 #-}

-- The termination checker faultily accepts this call pattern
-- (with termination depth 2)
--
--   f (suc n , _)           = g (n ,_)
--   f (n     , suc (suc m)) = f (suc n , m)
--   g h                     = f (h 2)
--
-- but if you inline g, the loop is detected:
--
--   f (suc n , _)           = f (n     , 2)
--   f (n     , suc (suc m)) = f (suc n , m)

-- Primitive types

data ⊥ : Set where
record ⊤ : Set where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

data _≡_ (A : Set) : Set → Set₁ where
  refl : A ≡ A

cast : ∀{A B : Set} → A ≡ B → A → B
cast refl x = x

cast⁻¹ : ∀{A B : Set} → A ≡ B → B → A
cast⁻¹ refl x = x

-- Exploit the termination checker bug to prove ⊥.

data D : Set where
  _,_ : Nat → Nat → D

P : D → Set
P (suc _ , _)           = ⊥
P (_     , suc (suc _)) = ⊥
P (0 , 0) = ⊤
P (0 , 1) = ⊤

-- This does not hold definitionally (no exact split), so prove it.
lem : ∀ n {m} → P (n , suc (suc m)) ≡ ⊥
lem 0       = refl
lem (suc n) = refl

mutual
  f : (x : D) → P x
  -- The loop:
  f (suc n , _)           = cast   (lem n) (g (n ,_))       -- this call to g is fishy!
  f (n     , suc (suc m)) = cast⁻¹ (lem n) (f (suc n , m))
  -- Base cases:
  f (0 , 0) = record{}
  f (0 , 1) = record{}

  g : (h : Nat → D) → P (h 2)
  g h = f (h 2)

loop : ⊥
loop = f (1 , 0)
