-- Andreas, 2017-06-16, issue #2604:
-- Symbolic anchors in generated HTML.

module Issue2604 where

test1 : Set₁  -- Symbolic anchor
test1 = bla
  where
  bla = Set   -- Position anchor

test2 : Set₁  -- Symbolic anchor
test2 = bla
  where
  bla = Set   -- Position anchor

test3 : Set₁  -- Symbolic anchor
test3 = bla
  module M where
  bla = Set  -- Symbolic anchor

module NamedModule where
  test4 : Set₁  -- Symbolic anchor
  test4 = M.bla

module _ where
  test5 : Set₁  -- Position anchor
  test5 = M.bla

-- Testing whether # in anchors confuses the browsers.
-- Not Firefox 54.0, at least (Andreas, 2017-06-20).

# : Set₁
# = Set

#a : Set₁
#a = #

b# : Set₁
b# = #a

## : Set₁
## = b#
