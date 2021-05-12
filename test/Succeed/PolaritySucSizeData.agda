-- Andreas, 2015-07-01 polarity of the size argument to data
-- needs to be considered for polarity of later definitions.

-- {-# OPTIONS -v tc.pos:10 -v tc.polarity:20 #-}

{-# OPTIONS --sized-types #-}

open import Common.Size
open import Common.Prelude

data D : (i : Size) → Set where
  c : ∀ i → D (↑ i)

E : Bool → Size → Set
E true  i = D i
E false i = D i

cast : ∀{i b} → E b i → E b (↑ i)
cast x = x

-- should succeed
