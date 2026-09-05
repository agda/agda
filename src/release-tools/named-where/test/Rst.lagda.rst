Restructured text literate test
===============================

A decoy in prose: module Decoy where

::

    module Rst where

    open import Agda.Builtin.Bool
    open import Agda.Builtin.Nat

    h : Bool → Nat
    h b with b
    ... | true  = 0
    ... | false = 1
      module W where
      q : Nat
      q = 1

Back to prose: module Decoy2 where
