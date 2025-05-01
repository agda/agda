-- Andreas, 2025-05-01, issue #7839, evidence that POLARITY is unsafe.
-- This proof of False was contributed by Guillaume Allais.

{-# OPTIONS --safe #-}

variable A : Set

data ⊥ : Set where

postulate
  Not : Set → Set
  putNot : (A → ⊥) → Not A
  getNot : Not A → (A → ⊥)

{-# POLARITY Not ++ #-}

data Oops : Set where
  mkOops : Not Oops → Oops

noops : Oops → ⊥
noops o@(mkOops n) = getNot n o

boom : ⊥
boom = noops (mkOops (putNot noops))
