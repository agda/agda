-- {-# OPTIONS -v tc.conv.coerce:10 -v tc.conv.size:40 -v tc.size.solve:40 #-}
-- Andreas, 2014-06-16 Coercion for sizes
open import Common.Size

data Nat (i : Size) : Set where
  zero : Nat i
  suc  : (j : Size< i) → Nat j → Nat i

three : (i : Size) → Nat (↑ ↑ ↑ i)
three i = suc _ (suc _ (suc i zero))

-- Should be ok, but we get the error:
-- ∞ !=< i of type Size
-- when checking that the expression _ has type Size< (↑ (↑ (↑ i)))

-- Works now.
