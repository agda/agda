-- Andreas, 2016-07-28, issue #779

record R : Set1 where

  Bla : Set1
  Bla with Set
  ... | _ = Set

  field
    F : Set

-- With-abstraction can precede a later field.
