-- Andreas, 2025-04-16, regression #7807 introduced in #7645
-- Report, testcase and bisection by Szumi Xie

-- {-# OPTIONS -v interaction.give:40 #-}

postulate
  _∘_ : (Set → Set) → (Set → Set) → Set → Set
  F : Set → Set
  A : Set

_ : Set
_ = {!F ∘ F!} A

-- Giving F ∘ F should insert parentheses
