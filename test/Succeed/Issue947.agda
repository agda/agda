
module Issue947 where

A : Set₁
A = Set
  where

B : Set₁
B = Set
  module _ where

C : Set₁
C = Set
  module M where

-- Andreas, 2020-04-25, #4623
-- These empty `where` blocks now generate warnings.
