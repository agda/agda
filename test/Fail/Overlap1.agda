module Overlap1 where

open import Agda.Builtin.Unit
open import Agda.Builtin.Int

postulate
  C   : Set → Set → Set
  instance
    CIa : ∀ {a} → C Int a
    CaI : ∀ {a} → C a Int
  {-# OVERLAPS CIa CaI #-}

use : ∀ a b → ⦃ C a b ⦄ → Set
use a b = ⊤

-- In this use site, neither instance is strictly more specific than the
-- other, so neither overrides the other. The constraint is stuck.

_ : use Int Int
_ = tt
