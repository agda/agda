-- Andreas, 2017-01-01, issue #2377
-- Warn about useless `public` in `open` statements.

-- {-# OPTIONS -v scope.decl:70 #-}

-- Warning #1
open import Agda.Builtin.Nat public

import Agda.Builtin.Bool as B

-- Warning #2
open B public

module _ where

open import Agda.Builtin.Equality public -- no warning

-- Warning #3
test-let : Set₁
test-let = let open B public in Set

-- Warning #4
test-letm : Set₁
test-letm = let open module C = B public in Set
