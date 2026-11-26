-- Andreas, 2016-07-28, issue #779

record R : Set1 where
  module Bla where
  field F : Set

-- A module declaration can precede a later field.
