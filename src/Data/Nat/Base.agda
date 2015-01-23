------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers, basic types and operations
------------------------------------------------------------------------

module Data.Nat.Base where

import Level using (zero)
open import Relation.Binary.Core
open import Relation.Nullary using (¬_)

infix 4 _≤_ _<_ _≥_ _>_ _≰_ _≮_ _≱_ _≯_

------------------------------------------------------------------------
-- The types

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

data _≤_ : Rel ℕ Level.zero where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

{-# BUILTIN NATURAL ℕ #-}

infixl 6 _+_ _∸_
infixl 7 _*_

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATPLUS _+_ #-}

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n

{-# BUILTIN NATMINUS _∸_ #-}

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n

{-# BUILTIN NATTIMES _*_ #-}

_<_ : Rel ℕ Level.zero
m < n = suc m ≤ n

_≥_ : Rel ℕ Level.zero
m ≥ n = n ≤ m

_>_ : Rel ℕ Level.zero
m > n = n < m

_≰_ : Rel ℕ Level.zero
a ≰ b = ¬ a ≤ b

_≮_ : Rel ℕ Level.zero
a ≮ b = ¬ a < b

_≱_ : Rel ℕ Level.zero
a ≱ b = ¬ a ≥ b

_≯_ : Rel ℕ Level.zero
a ≯ b = ¬ a > b

-- The following, alternative definition of _≤_ is more suitable for
-- well-founded induction (see Induction.Nat).

infix 4 _≤′_ _<′_ _≥′_ _>′_

data _≤′_ (m : ℕ) : ℕ → Set where
  ≤′-refl :                         m ≤′ m
  ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ suc n

_<′_ : Rel ℕ Level.zero
m <′ n = suc m ≤′ n

_≥′_ : Rel ℕ Level.zero
m ≥′ n = n ≤′ m

_>′_ : Rel ℕ Level.zero
m >′ n = n <′ m

------------------------------------------------------------------------
-- A generalisation of the arithmetic operations

fold : {a : Set} → a → (a → a) → ℕ → a
fold z s zero    = z
fold z s (suc n) = s (fold z s n)

module GeneralisedArithmetic {a : Set} (0# : a) (1+ : a → a) where

  add : ℕ → a → a
  add n z = fold z 1+ n

  mul : (+ : a → a → a) → (ℕ → a → a)
  mul _+_ n x = fold 0# (λ s → x + s) n

------------------------------------------------------------------------
-- Arithmetic

pred : ℕ → ℕ
pred zero    = zero
pred (suc n) = n

infixl 7 _⊓_
infixl 6 _+⋎_ _⊔_

-- Argument-swapping addition. Used by Data.Vec._⋎_.

_+⋎_ : ℕ → ℕ → ℕ
zero  +⋎ n = n
suc m +⋎ n = suc (n +⋎ m)

-- Max.

_⊔_ : ℕ → ℕ → ℕ
zero  ⊔ n     = n
suc m ⊔ zero  = suc m
suc m ⊔ suc n = suc (m ⊔ n)

-- Min.

_⊓_ : ℕ → ℕ → ℕ
zero  ⊓ n     = zero
suc m ⊓ zero  = zero
suc m ⊓ suc n = suc (m ⊓ n)

-- Division by 2, rounded downwards.

⌊_/2⌋ : ℕ → ℕ
⌊ 0 /2⌋           = 0
⌊ 1 /2⌋           = 0
⌊ suc (suc n) /2⌋ = suc ⌊ n /2⌋

-- Division by 2, rounded upwards.

⌈_/2⌉ : ℕ → ℕ
⌈ n /2⌉ = ⌊ suc n /2⌋
