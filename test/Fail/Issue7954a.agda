-- Andreas, 2025-07-16, issue #7954.
-- Do not allow parentheses around postfix projections.

module _ where

record R (A : Set) : Set where
  field
    proj : A
open R

example1 : {A : Set} → R A → A
example1 r = r .(proj)

-- Expected error: [InvalidDottedExpression]
-- Invalid dotted expression
-- when scope checking .(proj)
