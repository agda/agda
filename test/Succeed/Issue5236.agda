-- Andreas, 2021-04-19, fixed #5236, regression introduced by #2858.
-- In record declarations, `constructor` should not be a layout keyword,
-- in order to be compatible with Agda 2.6.1.

record Works : Set₁ where
  eta-equality; field
    W : Set

record Test : Set₁ where
  constructor c; field
    F : Set   -- Should work

record Test2 : Set₁ where
  constructor c; eta-equality -- Should work
  field
    foo : Set
