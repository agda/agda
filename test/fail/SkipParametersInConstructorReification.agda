-- Andreas, 2012-04-20
{-# OPTIONS --show-implicit #-}
module SkipParametersInConstructorReification where

data Bool : Set where
  true false : Bool

data D (A : Set) : Set where
  c : {regArg : A} -> D A

data P : {A : Set} → D A → Set where
  p : P (c {regArg = true})

bla : Set
bla with c {regArg = true}
bla | _ = Bool

fail : P (c {regArg = false})
fail = true

-- What counts here is the error message!
--
--   Bool !=< P {Bool} (c {regArg = false}) of type Set
--
-- the parameter argument of c should be skipped, but the
-- regular argument should show up
