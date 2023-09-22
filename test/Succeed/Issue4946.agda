-- Andreas, 2020-09-26, issue #4946.
-- More liberal type signatures for constructors of sized types.

-- {-# OPTIONS -v tc.polarity:20 #-}
{-# OPTIONS --sized-types --large-indices #-}

open import Agda.Builtin.Size

variable
  i : Size
  A : Set

data T : Size → Set → Set where
  c : A → T i A → T (↑ i) A

-- The type of the constructor c is elaborated to
--
--   c : {A : Set} {i : Set} → A → T i A → T (↑ i) A
--
-- Thus, the size argument i is not the first.
-- Nevertheless, Agda recognize the first argument of T
-- as covariant.

test : T i A → T ∞ A
test x = x

-- Should pass.
