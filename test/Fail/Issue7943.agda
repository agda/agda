{-# OPTIONS --erasure #-}
{-# OPTIONS --without-K #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.IO
open import Agda.Builtin.Unit

postulate
  print : Nat → IO ⊤

{-# COMPILE GHC print = print #-}

@0 er5 : Nat
er5 = 5

record R : Set₂ where
  field
    @0 f : Set₁

foo : R
foo .R.f = Set
  module @ω M where  -- @ω is ignored here
    five : Nat
    five = er5
    -- Either five should be marked as erased,
    -- or one should not be able to refer to er5.

main = print M.five  -- Error, because M.five is erased

-- error: [DefinitionIsErased]
-- Identifier M.five is declared erased, so it cannot be used here
-- when checking that the expression M.five has type Nat
