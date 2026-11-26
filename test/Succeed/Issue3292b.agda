
module _ where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

module Vars (A : Set) where
  variable
    x : A

-- The field is checked in an ordinary module, so opened generalizable
-- variables no longer go through a telescope let.
record R : Set₁ where
  field
    A : Set
  open Vars A
  field
    f : x ≡ x
