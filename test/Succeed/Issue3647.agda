-- Andreas, 2019-03-25, issue #3647, reported and bisected by nad.
-- Regression introduced in refactoring a78d7f54e447cadf039da81b50ff40c81aa93909.

{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS -v 90 #-}

postulate
  A : Set
  P : A → Set

Q : A → A → Set
Q _ x = P x

record R (P : A → Set) : Set where
  field f : (x : A) → P x → P x

open R ⦃ … ⦄

module M {x : A} where

  instance
    postulate
      r₁ r₂ : R (Q x)

postulate
  q₁ : (x : A) → P x

q₂ : (x : A) → P x
q₂ x = f _ (q₁ x)

-- WAS: internal error.

-- Should succeed with unsolved metas.
