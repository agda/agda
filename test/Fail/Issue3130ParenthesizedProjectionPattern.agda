-- Andreas, 2018-06-19, issue #3130
-- Do not treat .(p) as projection pattern, but always as dot pattern.

record R : Set₁ where
  field f : Set
open R

-- Shouldn't pass.

mkR : (A : Set) → R
mkR A .(f) = A
