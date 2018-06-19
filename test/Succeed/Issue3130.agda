-- Andreas, 2018-06-19, issue #3130

-- A pattern variable should not shadow a postfix projection
-- in the same scope.

record R : Set₁ where
  field y : Set → Set
open R

-- Should succeed or maybe complain about pattern variable y,
-- but not about the postfix projection pattern.

test : R
test .y y = y
