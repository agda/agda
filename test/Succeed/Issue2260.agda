-- Andreas, 2016-10-14, issue #2260 testcase by Nisse

-- {-# OPTIONS -v tc.meta:40 #-}

data D : Set → Set₁ where
  d : (A : Set) → D A

postulate
  A : Set
  f : (A : Set) → D A → D A

B : Set₁
B = Set
  where
  abstract

    A′ : Set
    A′ = A

  x : D A′
  x = f _ (d A′)

-- WAS: internal error
-- should check
