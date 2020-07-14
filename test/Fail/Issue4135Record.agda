-- Andreas, 2020-06-17, issue #4135
-- Do not allow meta-solving during projection disambiguation!

data Bool : Set where
  true false : Bool

module Foo (b : Bool) where
  record R : Set where
    field f : Bool
  open R public

open module True  = Foo true
open module False = Foo false

test : Foo.R {!!}
test .f = {!!}

-- WAS: succeeds with constraint ?0 := true
-- C-c C-=

-- Expected error:
-- Ambiguous projection f.
-- It could refer to any of
--   True.f (introduced at <open module True>)
--   False.f (introduced at <open module False>)
-- when checking the clause left hand side
-- test .f
