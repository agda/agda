-- Andreas, 2015-07-01, Issue 1599:
-- abstract data needs to be positivity checked!

-- {-# OPTIONS -v tc.pos:80 #-}

data ⊥ : Set where

abstract

  T : Set → Set
  T X = X → ⊥

  data D : Set where
    lam : T D → D

  app : D → D → ⊥
  app (lam f) = f

  omega : D
  omega = lam λ x → app x x

  Omega : ⊥
  Omega = app omega omega

absurd : ⊥
absurd = Omega
