-- Andreas, 2012-07-31 no eager introduction of hidden abstractions
{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.conv.coerce:100 #-}
-- {-# OPTIONS -v tc.with:100 #-}
module Issue679 where

data Unit : Set where
  unit : Unit

-- works also now:
test : {u : Unit} → Unit
test = λ {u} → u

T : Unit → Set
T unit = {u : Unit} → Unit

works : (u : Unit) → T u
works unit = λ {u} → u

fails : (u : Unit) → T u
fails unit with unit
... | _ = λ {u} → u

-- Error was:
-- {u : _14 _} → _16 _ !=< Unit of type Set
-- when checking that the expression λ {u} → u has type Unit

