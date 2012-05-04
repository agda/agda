
module Issue442 where

postulate
  A : Set
  f : (P : A → A → Set) → (∀ {x} → P x x) →
      (∀ {x y z} → P y z → P x y → A) → A
  P : A → A → Set
  reflP : ∀ {x} → P x x
  g : ∀ {x y z} → P y z → P x y → A

a : A
a = f _ (λ {x} → reflP {x}) g

-- Test case was:
-- {-# OPTIONS --allow-unsolved-metas #-}
-- a = f _ reflP g
