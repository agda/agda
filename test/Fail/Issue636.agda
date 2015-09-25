-- Andreas, 2012-05-14, issue reported by Nisse
-- {-# OPTIONS -v term:20 #-}
module Issue636 where

open import Common.Coinduction

data ⊥ : Set where

data D : Set where
  c : ∞ D → D

d : D
d = c (♯ d)

not-d : D → ⊥
not-d (c x) = not-d (♭ x)

bad : ⊥
bad = not-d d
