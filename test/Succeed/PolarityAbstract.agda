-- Andreas, 2015-07-01 polarity needs to be computed for abstract defs.
-- See also issue 1599 for the same problem with positivity.

-- {-# OPTIONS -v tc.pos:10 -v tc.polarity:20 #-}

open import Common.Size
open import Common.Prelude

data D (i : Size) : Set where
  c : ∀ (j : Size< i) → D i

abstract
  E : Bool → Size → Set
  E true  i = D i
  E false i = D i

  cast : ∀{i b} → E b i → E b (↑ i)
  cast x = x

-- should succeed
