
open import Agda.Builtin.Nat

record C (A : Set) : Set where

module M (X : Set) where
  module Ci = C {{...}}

module CiNat = M.Ci Nat -- error: The module M.Ci is not parameterized...
