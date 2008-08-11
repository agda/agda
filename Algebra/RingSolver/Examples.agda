------------------------------------------------------------------------
-- Some examples showing the solver in action
------------------------------------------------------------------------

-- Warning: This module requires lots of resources to type check.

module Algebra.RingSolver.Examples where

open import Data.Vec
open import Data.Fin
open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool
open import Data.Bool.Properties
open import Algebra
import Algebra.Operations as Ops
open Ops (CommutativeSemiring.semiring ℕ-commutativeSemiring)
  using (_^_)
open Ops (CommutativeRing.semiring Bool-commutativeRing-xor-∧)
  renaming (_^_ to _↑_)

example₁
  :  forall x y
  -> (x + y) ^ 3 ≡ x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3
example₁ x y =
  prove (x ∷ y ∷ [])
        ((X :+ Y) :^ 3)
        (X :^ 3 :+ con 3 :* X :^ 2 :* Y :+
         con 3 :* X :* Y :^ 2 :+ Y :^ 3)
        ≡-refl
  where
  open ℕ-semiringSolver
  X = var (# 0)
  Y = var (# 1)

-- The following example is commented out because it is (currently)
-- too slow.

-- example₂
--   :  forall x y
--   -> (x xor y) ↑ 3 ≡
--      (x ↑ 3) xor ((x ↑ 2) ∧ y) xor (x ∧ (y ↑ 2)) xor (y ↑ 3)
-- example₂ x y =
--   prove (x ∷ y ∷ [])
--         ((X :+ Y) :^ 3)
--         (X :^ 3 :+ (X :^ 2 :* Y :+ (X :* Y :^ 2 :+ Y :^ 3)))
--         ≡-refl
--   where
--   open Bool-xor-ringSolver
--   X = var (# 0)
--   Y = var (# 1)

example₃ : forall x -> x xor x ≡ false
example₃ x = prove (x ∷ []) (X :+ X) (con false) ≡-refl
  where
  open Bool-xor-ringSolver
  X = var (# 0)
