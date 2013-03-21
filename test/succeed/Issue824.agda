-- {-# OPTIONS -v tc.with.strip:40 #-}
module Issue824 where

record R : Set where

data D : Set → Set₁ where
  d : ∀ {A} → D A → D A

postulate
  d′ : D R

data P : R → D R → Set₁ where
  p : {x : R} {y : D R} → P x y → P x (d y)

Foo : P _ (d d′) → Set₁
Foo (p _) with Set
Foo (p _) | _ = Set

-- Bug.agda:18,1-19,20
-- Inaccessible (dotted) patterns from the parent clause must also be
-- inaccessible in the with clause, when checking the pattern
-- {.Bug.recCon-NOT-PRINTED},
-- when checking that the clause
-- Foo (p _) with unit
-- Foo (p _) | _ = Set
-- has type P (record {}) (d d′) → Set₁

-- See also issue 635 and issue 665.

-- Andreas, 2013-03-21: should work now.
