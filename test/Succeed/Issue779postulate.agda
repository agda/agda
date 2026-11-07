-- Andreas, 2016-07-28, issue #779

record P : Set₁ where
  postulate Bla : Set
  field F : Set

-- A postulate can precede a later field.
