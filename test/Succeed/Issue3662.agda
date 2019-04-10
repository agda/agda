-- Andreas, 2018-04-10, issue #3662.

-- Regression in the termination checker introduced together
-- with collecting function calls also in the type signatures
-- (fix of #1556).

record T : Set₂ where
  field
    Carr : Set₁
    op   : Carr → Carr

test : T
T.Carr test   = Set
T.op   test c = Aux
  where
  postulate Aux : Set
  --  Aux : (c : T.Carr test) → Set
  --             ^^^^^^^^^^^

-- Since c as a module parameter to the where-module is parameter of Aux,
-- it contains a recursive call if we also mine type signatures for calls
-- (#1556).
--
-- We get then
--
--   test .op c --> test .Carr
--
-- which is not a decreasing call.

-- However, the call does not compose with itself, thus, with
-- Hyvernat-termination it would not give a false termination alarm.

-- Should termination check.
