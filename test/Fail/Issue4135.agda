-- Andreas, 2020-06-17, issue #4135
-- Constructor disambiguation on should only instantiate metas
-- in a unique way.

-- {-# OPTIONS -v tc.lhs:10 #-}
-- {-# OPTIONS -v tc.lhs.split:40 #-}
-- {-# OPTIONS -v tc.lhs.disamb:40 #-}

data Bool : Set where
  true false : Bool

module Foo (b : Bool) where

  data D : Set where
    c : D

open module True  = Foo true
open module False = Foo false

test : Foo.D ? → Set
test c = ?

-- C-c C-=

-- EXPECTED ERROR:
-- Ambiguous constructor c.
-- ...
-- when checking that the pattern c has type Foo.D ?0
