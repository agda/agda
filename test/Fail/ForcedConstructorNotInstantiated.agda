-- Andreas, 2024-07-21, PR #7379
-- Trigger error ForcedConstructorNotInstantiated

data D : Set where
  c : D → D

f : D → Set
f (.c x) = D

-- Expected error:
-- Failed to infer that constructor pattern unit x is forced
-- when checking that the pattern unit x has type Unit
