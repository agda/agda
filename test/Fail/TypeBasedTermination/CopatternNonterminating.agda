-- Andreas, 2024-05-16, issue #7278
-- TBT: Missing function name in termination error.

{-# OPTIONS --no-syntax-based-termination #-}
{-# OPTIONS --type-based-termination #-}

module TypeBasedTermination.CopatternNonterminating where

open import Agda.Builtin.Equality

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
module S = Stream

illdefined : {A : Set} → Stream A
S.head illdefined = S.head illdefined
S.tail illdefined = S.tail illdefined
-- should not termination-check

-- Reports error without function name:
--
-- Termination checking failed for the following functions:
-- Problematic calls:
