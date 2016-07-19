-- {-# OPTIONS -v tc:30 #-}
-- Andreas, 2016-07-19, issue #2102

-- An abstract definition in a where block should not
-- stop metas of parent function to be solved!

test : _
test = Set  -- WAS: yellow
  where
  abstract def = Set

-- should succeed

test1 = Set
  module M where
  abstract def = Set

-- Similar situation

mutual
  test2 : _
  abstract def = Set
  test2 = Set
