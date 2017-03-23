-- Andreas, 2017-03-23, issue #2510
-- Error message in case of --no-pattern-matching

{-# OPTIONS --no-pattern-matching #-}

test : Set
test x = x

-- Expected error:
-- Cannot eliminate type Set with pattern x (did you supply too many arguments?)
