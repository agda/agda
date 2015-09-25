-- Andreas, 2013-11-11 Better error for wrongly named implicit arg.
module Issue949 where

postulate
  S   : Set
  F   : {A : Set} → Set
  ok  : F {A = S}
  err : F {B = S}

-- Old error:
--
-- Set should be a function type, but it isn't
-- when checking that {B = S} are valid arguments to a function of
-- type Set

-- New error (after fixing also issue 951):
--
-- Function does not accept argument {B = _}
-- when checking that {B = S} are valid arguments to a function of
-- type {A : Set} → Set
