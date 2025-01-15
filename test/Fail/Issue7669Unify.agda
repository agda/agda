-- Andreas, 2025-01-13, #7674, test by Szumi Xie

data Unit : Set where
  tt : Unit

postulate
  A B : Set

FUN : Set₁
FUN = Set → Set

ConstA : Unit → FUN
ConstA tt _ = A

postulate
  x : Unit
  f : (Z : Set) → ConstA x Z

a : ConstA x B
a = f _  -- This meta should remain unsolved because of non-variant polarity.
