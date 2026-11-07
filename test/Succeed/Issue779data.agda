-- Andreas, 2016-07-28, issue #779

record R : Set1 where
  data Bla : Set where
  field F : Set

-- A datatype declaration can precede a later field.
