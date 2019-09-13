-- Andreas, 2019-09-13, AIM XXX, test for #4050 by gallais

record Wrap : Set₂ where
  field wrapped : Set₁

f : Wrap
f = record { M }
  module M where
    wrapped : Set₁
    wrapped = Set

-- Should be accepted.
