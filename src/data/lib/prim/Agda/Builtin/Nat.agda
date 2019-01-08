{-# OPTIONS --without-K --safe --no-universe-polymorphism --no-sized-types --no-guardedness #-}

module Agda.Builtin.Nat where

open import Agda.Builtin.Bool

data Nat : Set where
  zero : Nat
  suc  : (n : Nat) → Nat

{-# BUILTIN NATURAL Nat #-}

infix  4 _==_ _<_
infixl 6 _+_ _-_
infixl 7 _*_

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)

{-# BUILTIN NATPLUS _+_ #-}

_-_ : Nat → Nat → Nat
n     - zero = n
zero  - suc m = zero
suc n - suc m = n - m

{-# BUILTIN NATMINUS _-_ #-}

_*_ : Nat → Nat → Nat
zero  * m = zero
suc n * m = m + n * m

{-# BUILTIN NATTIMES _*_ #-}

_==_ : Nat → Nat → Bool
zero  == zero  = true
suc n == suc m = n == m
_     == _     = false

{-# BUILTIN NATEQUALS _==_ #-}

_<_ : Nat → Nat → Bool
_     < zero  = false
zero  < suc _ = true
suc n < suc m = n < m

{-# BUILTIN NATLESS _<_ #-}

-- Helper function  div-helper  for Euclidean division.
---------------------------------------------------------------------------
--
-- div-helper computes n / 1+m via iteration on n.
--
--   n div (suc m) = div-helper 0 m n m
--
-- The state of the iterator has two accumulator variables:
--
--   k: The quotient, returned once n=0.  Initialized to 0.
--
--   j: A counter, initialized to the divisor m, decreased on each iteration step.
--      Once it reaches 0, the quotient k is increased and j reset to m,
--      starting the next countdown.
--
-- Under the precondition j ≤ m, the invariant is
--
--   div-helper k m n j = k + (n + m - j) div (1 + m)

div-helper : (k m n j : Nat) → Nat
div-helper k m  zero    j      = k
div-helper k m (suc n)  zero   = div-helper (suc k) m n m
div-helper k m (suc n) (suc j) = div-helper k       m n j

{-# BUILTIN NATDIVSUCAUX div-helper #-}

-- Proof of the invariant by induction on n.
--
--   clause 1: div-helper k m 0 j
--           = k                                        by definition
--           = k + (0 + m - j) div (1 + m)              since m - j < 1 + m
--
--   clause 2: div-helper k m (1 + n) 0
--           = div-helper (1 + k) m n m                 by definition
--           = 1 + k + (n + m - m) div (1 + m)          by induction hypothesis
--           = 1 + k +          n  div (1 + m)          by simplification
--           = k +   (n + (1 + m)) div (1 + m)          by expansion
--           = k + (1 + n + m - 0) div (1 + m)          by expansion
--
--   clause 3: div-helper k m (1 + n) (1 + j)
--           = div-helper k m n j                       by definition
--           = k + (n + m - j) div (1 + m)              by induction hypothesis
--           = k + ((1 + n) + m - (1 + j)) div (1 + m)  by expansion
--
-- Q.e.d.

-- Helper function  mod-helper  for the remainder computation.
---------------------------------------------------------------------------
--
-- (Analogous to div-helper.)
--
-- mod-helper computes n % 1+m via iteration on n.
--
--   n mod (suc m) = mod-helper 0 m n m
--
-- The invariant is:
--
--   m = k + j  ==>  mod-helper k m n j = (n + k) mod (1 + m).

mod-helper : (k m n j : Nat) → Nat
mod-helper k m  zero    j      = k
mod-helper k m (suc n)  zero   = mod-helper 0       m n m
mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j

{-# BUILTIN NATMODSUCAUX mod-helper #-}

-- Proof of the invariant by induction on n.
--
--   clause 1: mod-helper k m 0 j
--           = k                               by definition
--           = (0 + k) mod (1 + m)             since m = k + j, thus k < m
--
--   clause 2: mod-helper k m (1 + n) 0
--           = mod-helper 0 m n m              by definition
--           = (n + 0)       mod (1 + m)       by induction hypothesis
--           = (n + (1 + m)) mod (1 + m)       by expansion
--           = (1 + n) + k)  mod (1 + m)       since k = m (as l = 0)
--
--   clause 3: mod-helper k m (1 + n) (1 + j)
--           = mod-helper (1 + k) m n j        by definition
--           = (n + (1 + k)) mod (1 + m)       by induction hypothesis
--           = ((1 + n) + k) mod (1 + m)       by commutativity
--
-- Q.e.d.
