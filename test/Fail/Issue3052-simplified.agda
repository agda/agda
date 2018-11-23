-- Andreas & Jesper, 2018-05-11, issue #3052 reported by identicalsnowflake
--
-- The problem here was that free variable collection had the standard
-- monoid instance of IntMap, which is just "randomly" picking one variant.
-- Thus, if we have both irrelevant and relevant occurrences of a variable,
-- we get whatever.
-- Now we keep the stronger information (relevant, see maxVarOcc).

{-# OPTIONS --show-irrelevant #-}
-- {-# OPTIONS -v tc.meta.assign:100 -v tc.meta.occurs:45 #-}
-- {-# OPTIONS -v tc.lhs:100 #-}

postulate
  A : Set
  B : A → Set

record Σ : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ public

record Foo : Set where
  constructor foo
  field
    .theFoo : Σ

test : Foo → Foo
test (foo (a , b)) = foo (a , thm a b) -- Error at b
  -- Constraint: a, b ⊢ ?0 .a .b a = B a : Set
  -- Note the irrelevant occurrence .a and the relevant occurrence a
  -- on the lhs of this constraint!
  where
    -- Meta ?0 : [.a, .b, x] Set
    postulate thm : (x : A) (y : _) → B x
    -- Underscore should solved by B x
    -- thm x y = y -- WAS: Worked only if definition is given (which

-- Should succeed.

-- Jesper, 2018-11-23, This test case fails since the fix of #3056.
-- I'm not sure if there is a way to salvage this test case, but I leave
-- it in Fail in case anyone wants to try.
