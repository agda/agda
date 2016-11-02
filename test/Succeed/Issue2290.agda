-- Andreas, 2016-11-02, issue #2290

postulate
  A : Set
  a : A
  F : Set → Set

mutual
  data D : A → _ where
  FDa = F (D a)

-- ERROR WAS:
-- The sort of D cannot depend on its indices in the type A → Set _7

-- Should pass.

mutual
  data E : (x : A) → _ where
  FEa = F (E a)
