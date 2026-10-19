-- This import statement is included because a bug made Agda think
-- that the current module was Agda.Builtin.Equality, which led to the
-- code below being accepted.

open import Agda.Builtin.Equality

postulate
  [_] : Set

{-# BUILTIN QUOTIENTCONSTRUCTOR [_] #-}
