-- Andreas, 2019-10-21, issue #4142, reported and test case by Jason Hu

-- When the record-expression-to-copattern-translation is revisited
-- after positivity checking, the defCopatternLHS flag needs to be
-- updated as well!

-- {-# OPTIONS -v tc.cc.record:20 #-}
-- {-# OPTIONS -v tc.conv:30 #-}

open import Agda.Builtin.Equality

record WrapSet : Set1 where
  constructor wrap
  -- eta-equality -- WAS: needed for test
  field
    Wrapped : Set

  eta : WrapSet
  eta .Wrapped = Wrapped

  pack : WrapSet
  pack = record { Wrapped = Wrapped }

-- The positivity check makes WrapSet an eta-record after the fact.
-- Thus, the record-expression-to-copattern-translation is run again for pack.

open WrapSet

-- Make sure eta was inferred correctly for WrapSet

hasEta : (w : WrapSet) → w ≡ record{ Wrapped = Wrapped w }
hasEta w = refl

-- When we have a definition by copattern matching it works.

works : (w : WrapSet) → w ≡ eta w
works w = refl

-- Should also work for pack.

test : (w : WrapSet) → w ≡ pack w
test w = refl
