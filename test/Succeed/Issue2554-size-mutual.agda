-- Andreas, 2017-04-26, issue #2554
-- Allow mutual sized types in successor style.

-- {-# OPTIONS -v tc.pos:100 #-}
-- {-# OPTIONS -v tc.polarity:20 #-}

open import Agda.Builtin.Size

mutual

  data C : Size → Set where
    c : ∀{i} → D i → C (↑ i)

  data D : Size → Set where
    d : ∀{i} → C i → D (↑ i)

-- Test subtyping

test : ∀{i} {j : Size< i} → C j → C i
test x = x

-- Define a size-preserving function

mutual

  f : ∀{i} → C i → C i
  f (c y) = c (g y)

  g : ∀{i} → D i → D i
  g (d x) = d (f x)
