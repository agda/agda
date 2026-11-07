-- Andreas, 2016-07-28, issue #779

record R : Set1 where
  record Bla : Set where
  field F : Set

-- A record declaration can precede a later field.
