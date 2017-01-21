-- Andreas, 2017-01-21, issue #2424

-- {-# OPTIONS -v tc.cover:40 #-}
-- {-# OPTIONS -v interaction.case:40 #-}

postulate Nat : Set

data List : Set₁ where
  _∷_ : (x : Set) (xs : List) → List

test : (As : List) (x : Nat) → Set
test As x = {!As!} -- C-c C-c

-- Expected output:
--   test (x₁ ∷ As) x = {!!}
