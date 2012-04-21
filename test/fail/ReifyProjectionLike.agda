-- Andreas, 2012-04-21
-- {-# OPTIONS -v tc.proj.like:100 -v tc.with:100 #-}
module ReifyProjectionLike where

data Maybe (A : Set) : Set where
  just    : A → Maybe A

fromJust : (A : Set) → Maybe A → A
fromJust A (just a) = a

data Sing (A : Set) : A -> Set where
  sing : (a : A) -> Sing A a

succeed : (A : Set) -> Maybe A -> Set
succeed A m with sing (fromJust A m)
... | _ = A

fail : (A : Set) -> Maybe A -> Set
fail A m with sing (fromJust A m)
... | (just x) = x

-- error message is wrong:
--
--   just is not a constructor of the datatype Sing
--   when checking that the pattern just x has type Sing A (fromJust m)
--
-- the "A" got dropped from "fromJust"
--
-- correct message is
--
--   just is not a constructor of the datatype Sing
--   when checking that the pattern just x has type Sing A (fromJust A m)
