-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.with.top:25 #-}
-- {-# OPTIONS -v tc.with:40 -v tc.interaction:20 -v interaction.give:20 -v tc:10 #-}

open import Common.Equality

data Unit : Set where
  unit : Unit

id : (A : Set) → A → A
id A a = a

module Works where

  dx : (x : Unit) → Unit → Unit
  dx x unit = x

  g : (x : Unit) → ∀ u → x ≡ dx x u
  g x with x
  g x | unit = id ((u : Unit) → unit ≡ dx unit u) ?

-- Now if we make (x : Unit) a module parameter
-- then we turn all applications (dx _) into just dx,
-- which actually means (dx x), i.e., dx applied to
-- the module free variables.

-- This leads to an incomprehendable rejection
-- of the following code (culprit is the first argument to id).

module M (x : Unit) where

  dx : Unit → Unit
  dx unit = x

  g : ∀ u → x ≡ dx u
  g with x
  g | unit  = id ((u : Unit) → unit ≡ dx u) ?

-- Now, `with x` is a plain error.

-- Also in harmless cases like the one below:

module CollateralDamage (x : Unit) where

  x′ = x

  bla : x ≡ x′
  bla with x
  bla | unit  = id (unit ≡ unit) refl

