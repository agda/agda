-- Andreas, 2016-06-21, issue #2054
-- Size solver should not default to ∞ in where block signatures

-- {-# OPTIONS --v tc.size:20 #-}

-- {-# BUILTIN SIZEUNIV SizeU #-}
-- {-# BUILTIN SIZE     Size   #-}
-- {-# BUILTIN SIZESUC  ↑_     #-}
-- {-# BUILTIN SIZEINF  ∞     #-}

open import Common.Size

data N : Size → Set where
  suc : ∀{i} (a : N i) → N (↑ i)

record R (j : Size) : Set where
  field num : N j

postulate
  W : ∀ {j} (ft : R j) → Set
  E : ∀ {j} (ft : R j) (P : (w : W ft) → Set) → Set

test : ∀ {j} (ft : R j) → Set
test {j} ft = E {j} ft testw
  where
    postulate
      testw : ∀ {ft : R _} (w : W ft) → Set

-- Should work
-- _ should not set to ∞, but to j
