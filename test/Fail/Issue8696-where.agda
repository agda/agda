-- Andreas, 2026-08-29, issue #8696
-- Issue found by Claude and reported by bdrisc-ant

-- This variant of Issue8689 places the module application in a where block
-- with the same effect as in a mutual block.
-- The copy F made in f's where block used to lose the occurrence of its parameter,
-- hence f's own second argument was judged unused (Nonvariant),
-- which could be exploited by getting a cast of ⊤ to ⊥.

{-# OPTIONS --safe --without-K #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Unit

data ⊥ : Set where

module M (A : Set) where
  data F (X : Set) : Set where
    mk : X → (X → A) → F X

f : Bool → Set → Set
f true  X = F X
  module W where
  open M ⊤ public
f false X = ⊥

-- This cast function should be rejected.
cast : (b : Bool) (X Y : Set) → f b X → f b Y
cast b X Y v = v

get : W.F ⊤ ⊥ → ⊥
get (W.mk b _) = b

boom : ⊥
boom = get (cast true ⊤ ⊥ (W.mk {⊤} tt (λ _ → tt)))
