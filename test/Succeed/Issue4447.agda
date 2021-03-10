-- Andreas, 2020-02-15, issue #4447, reported by zraffer

record Wrap : Set₁ where
  constructor ↑
  field ↓ : Set
open Wrap public

data Unit : Set

-- The type checker sees through this definition,
-- thus, the positivity checker should as well:
𝕌nit = ↑ Unit

data Unit where
  unit : ↓ 𝕌nit

-- WAS: internal error in the positivity checker.
