-- Agda should warn if a coinductive record is declared but neither
-- --guardedness nor --sized-types is enabled.

record R : Set where
  coinductive
  field
    r : R
