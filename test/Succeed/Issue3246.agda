-- Andreas, 2018-10-29, issue #3246

-- More things are now allowed in mutual blocks.

-- @mutual@ just pushes the definition parts to the bottom.
-- Definitions exist for data, record, functions, and pattern synonyms.

{-# OPTIONS --guardedness #-}

postulate Float : Set

{-# BUILTIN FLOAT Float #-}  -- not (yet) allowed in mutual block

mutual

  import Agda.Builtin.Bool
  open Agda.Builtin.Bool

  f : Bool
  f = g   -- pushed to bottom

  -- module M where  -- not (yet) allowed in mutual block

  module B = Agda.Builtin.Bool

  primitive
    primFloatEquality : Float → Float → Bool

  {-# INJECTIVE primFloatEquality #-}  -- certainly a lie

  open import Agda.Builtin.Equality
  {-# DISPLAY primFloatEquality x y = x ≡ y #-}

  postulate A : Set
  {-# COMPILE GHC A = type Integer #-}

  variable x : Bool

  g : Bool
  g = true  -- pushed to bottom

  {-# STATIC g #-}

  record R : Set where
    coinductive
    field foo : R

  {-# ETA R #-}
