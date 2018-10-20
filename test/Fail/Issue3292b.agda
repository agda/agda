
module _ where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

module Vars (A : Set) where
  variable
    x : A

-- Was
--   An internal error has occurred. Please report this as a bug.
--   Location of the error: src/full/Agda/TypeChecking/Reduce/Fast.hs:148
-- Should be
--   Cannot use generalized variable from let-opened module
record R : Set₁ where
  field
    A : Set
  open Vars A
  field
    f : x ≡ x
