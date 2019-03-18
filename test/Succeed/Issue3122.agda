-- Andreas, 2019-03-18, issue #3122, AIM XXIX
-- Also pick up hidden record fields from a module.

record R : Set₂ where
  field {f} : Set₁

module M where
  f : Set₁
  f = Set

r : R
r = record { M }

-- WAS: yellow
-- Should check.
