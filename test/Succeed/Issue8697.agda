-- Andreas, 2026-08-29, issue #8697
-- The serializer hash-consed the Doubles of an interface (Float literals
-- and fixity levels) in a dictionary keyed by Double with Haskell's Eq,
-- under which 0.0 == -0.0.  Thus, only the zero encountered first was
-- stored and the other one was read back with the opposite sign.
-- Yet the conflation of positive and negative zero leads to inconsistency
-- (issue #2169).

{-# OPTIONS --safe #-}

module Issue8697 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Float

open import Issue8697.Zeros

-- The signs of the zeros have to survive the round trip through the interface.

pos-is-positive : primFloatIsNegativeZero +zero ≡ false
pos-is-positive = refl

neg-is-negative : primFloatIsNegativeZero -zero ≡ true
neg-is-negative = refl  -- This failed in Agda < 2.9.

-- The other special values also have to survive.

nan-is-nan : primFloatIsNaN nan ≡ true
nan-is-nan = refl

inf-is-infinite : primFloatIsInfinite inf ≡ true
inf-is-infinite = refl

infinities-differ : primFloatLess -inf inf ≡ true
infinities-differ = refl
