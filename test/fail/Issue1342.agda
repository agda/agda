-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.with.top:25 #-}
-- {-# OPTIONS -v tc.with:40 -v tc.interaction:20 -v interaction.give:20 -v tc:10 #-}

open import Common.Equality

data Unit : Set where
  unit : Unit

id : (A : Set) → A → A
id A a = a

-- Now if we make (x : Unit) a module parameter
-- then we turn all applications (dx _) into just dx,
-- which actually means (dx x), i.e., dx applied to
-- the module free variables.

-- This leads to an incomprehendable rejection
-- of the following code (culprit is the first argument to id).

f : Unit → Unit
f x = unit
  where

  dx : Unit → Unit
  dx unit = x

  g : ∀ u → x ≡ dx u
  g with x
  g | unit  = id ((u : Unit) → unit ≡ dx u) ?

-- Here, `with x` is an error.

