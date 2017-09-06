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
-- However, the Nu Html Checker complains (someone else, later).

# : Set₁
# = Set

#a : Set₁
#a = #

b# : Set₁
b# = #a

## : Set₁
## = b#

-- The href attribute values #A and #%41 are (correctly?) treated as
-- pointers to the same destination by Firefox 54.0. To point to %41
-- one should use #%2541.

A : Set₁
A = Set

%41 : Set₁
%41 = A

-- Ampersands may need to be encoded in some way. The blaze-html
-- library takes care of encoding id attribute values, and we manually
-- replace ampersands with %26 in the fragment parts of href attribute
-- values.

&amp : Set₁
&amp = Set

&lt : Set₁
&lt = &amp

-- Test of fixity declarations. The id attribute value for the
-- operator in the fixity declaration should be unique.

infix 0 _%42∀_

_%42∀_ : Set₁
_%42∀_ = Set

-- The following two variants of the character Ö should result in
-- distinct links.

Ö : Set₁
Ö = Set

Ö : Set₁
Ö = Ö
