-- Issue #8866: overlap resolution must not commit to a more specific
-- candidate when that candidate solves a metavariable of the goal type.

module Issue8866 where

open import Agda.Builtin.Unit

postulate
  C     : Set → Set
  X Y Z : Set

instance postulate
  gen  : ∀ {A : Set} → C A
  spec : C Z

{-# INCOHERENT spec #-}

postulate
  g  : ∀ {B : Set} ⦃ _ : C B ⦄ → B
  K  : Set → Set → Set
  op : ∀ {Q R : Set} ⦃ _ : K Q R ⦄ → ⊤ → Q → R

instance postulate
  k : ∀ {A : Set} → K A A

-- Accepted by 2.8.0, rejected by 2.9.0-rc1.
test : X → Y
test = op tt (λ x → g)

-- Rejected also by 2.8.0.
test' : X → Y
test' = op tt (λ (x : X) → g)

-- Overlap is still resolved when the goal is known.
test'' : Z
test'' = g
