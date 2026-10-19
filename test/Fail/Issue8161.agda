-- Andreas, 2025-12-30, reproducer for #8161/RefinedContext.
-- Submitted by Amelia Lao, to be mentioned honorably.

module Issue8161 where

open import Agda.Builtin.Nat

data The {ℓ} (A : Set ℓ) : A → Set ℓ where
  yk : ∀ x → The A x

data Is0 : Nat → Set where
  yep : Is0 0

postulate
  same : {A : Set} {x : A} (it : The A x) → The (The A x) it → Set

case_of_ : ∀ {ℓ} {A : Set} {B : Set ℓ} → A → (A → B) → B
case x of f = f x

variable
  A : Set
  x : A
  it : The A x

postulate
  a : {n : Nat} (arg : Is0 n) → case arg of λ { yep → same _ it  }

-- Expected error: [GeneralizationPrepruneErrorRefinedContext]
-- Failed to generalize because some of the generalized variables
-- depend on an unsolved meta created in a refined context (not a
-- simple extension of the context where generalization happens). The
-- problematic unsolved meta is
--   _A_46 at Issue8161.agda:22.55-59
-- when checking that _ it are valid arguments to a function of type
-- {A : Set} {x : A} (it : The A x) → The (The A x) it → Set
