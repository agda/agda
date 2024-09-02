{-# OPTIONS --no-keep-pattern-variables #-}

-- Andreas, 2017-09-03, issue #2729.
-- Expect non-indexed or -primed variables when splitting.

-- {-# OPTIONS -v interaction.case:100 #-}
-- {-# OPTIONS -v tc.cover:40 #-}

data Size : Set where
  ↑ : Size → Size

data Nat : Size → Set where
  zero : ∀ i → Nat (↑ i)
  suc  : ∀ i → Nat i → Nat (↑ i)

pred : ∀ i → Nat i → Nat i
pred i x = {!x!}  -- C-c C-c

-- WRONG (agda-2.5.3):
-- pred .(↑ i₁) (zero i₁) = ?
-- pred .(↑ i₁) (suc i₁ x) = ?

-- EXPECTED (correct in agda-2.5.1.1):
-- pred .(↑ i) (zero i) = ?
-- pred .(↑ i) (suc i x) = ?
