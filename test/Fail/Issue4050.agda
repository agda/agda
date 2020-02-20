-- Andreas, 2019-09-13, AIM XXX, test for #4050 by gallais

-- Jesper, 2019-12-19, moved to test/Fail after unfix of #3823

record Wrap : Set₂ where
  field wrapped : Set₁

f : Wrap
f = record { M }
  module M where
    wrapped : Set₁
    wrapped = Set

-- Should be accepted.
