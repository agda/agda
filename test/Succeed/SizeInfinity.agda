-- Andreas, 2016-02-21 issue 1862 reported by nad
-- {-# OPTIONS -v tc.decl:10 -v tc.def.where:10 -v tc.meta:10 -v tc.size.solve:100 #-}

{-# OPTIONS --sized-types #-}

open import Common.Size

data Nat (i : Size) : Set where
  zero : Nat i
  suc  : (j : Size< i) (n : Nat j) → Nat i

id : ∀ i → Nat i → Nat i
id _ zero      = zero
id _ (suc j n) = s
  where
    mutual
      s = suc _ r  -- should not be instantiated to ∞x
      r = id _ n
