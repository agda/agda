-- Andreas, 2018-06-19, issue #3130

module Issue3130 where

-- A pattern variable should not shadow a postfix projection
-- in the same scope.

module Shadow where

  record R : Set₁ where
    field y : Set → Set
  open R

  -- Should succeed or maybe complain about pattern variable y,
  -- but not about the postfix projection pattern.

  test : R
  test .y y = y

-- Disambiguation

module Parens where

  record R : Set₁ where
    field p : Set
  open R

  data D : (R → Set) → Set₁ where
    c : D p

  test : (f : R → Set) (x : D f) → Set₁
  test .(p) c = Set
