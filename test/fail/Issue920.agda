-- Andreas, 2013-10-25 issue reported by Jesper Cockx
-- simplified test case by Nisse

-- {-# OPTIONS -v tc.meta:30 #-}

module Issue920 where

import Common.Level

postulate
  Eq    : (A : Set) (x : A) → A → Set
  cast  : (A B : Set) → A → B
  magic : (P : Set → Set) (A : Set) → P A

bad : (A : Set) (x : A) → Eq A (cast A A x) x
bad A x = magic (λ B → Eq B (cast A B x) {!x!}) A

-- Should produce yellow, since there is no solution for ?0

-- Handling of linearity in constraint solver was buggy:
--   ?0 : (A : Set) (x : A) (B : Set) -> B
--   ?0 A x A := x
-- was simply solved by ?0 := λ A x B → x
-- since the non-linear variable did not appear on the rhs.
-- However, this solution is ill-typed.

-- Instead, we now only attempt pruning in case of non-linearity,
-- which fails here: B cannot be pruned since its the return type,
-- and A cannot be pruned since its the type of argument x.

