-- Andreas, 2017-08-24, issue #2253
--
-- Better error message for matching on abstract constructor.

-- {-# OPTIONS -v tc.lhs.split:30 #-}
-- {-# OPTIONS -v tc.lhs:30 #-}
-- {-# OPTIONS -v tc.lhs.flex:60 #-}

abstract
  data B : Set where
    x : B

data C : Set where
  c : B → C

f : C → C
f (c x) = c x

-- WAS:
--
-- Not in scope:
--   AbstractPatternShadowsConstructor.B.x
--     (did you mean 'x'?)
-- when checking that the pattern c x has type C

-- Expected:
--
-- Cannot split on abstract data type B
-- when checking that the pattern x has type B
