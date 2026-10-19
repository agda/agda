------------------------------------------------------------------------
-- The function []-cong
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe --no-sized-types
            --no-guardedness --level-universe
            --erased-matches=restricted #-}

-- The flag --erased-matches=restricted turns on all kinds of erased
-- matches for indexed data types, but only in certain builtin
-- modules. The code below must only give access to []-cong, no other
-- forms of erased matches.

module Agda.Builtin.Erased.Box-cong where

open import Agda.Builtin.Equality
open import Agda.Builtin.Erased.Erased
open import Agda.Primitive

private variable
  a      : Level
  @0 A   : Set a
  @0 x y : A

-- Given an erased proof of equality of x and y one can show that
-- [ x ] is equal to [ y ].
--
-- Note that this function cannot at the time of writing be
-- implemented in regular Agda code (unless
-- --erased-matches=unrestricted is turned on).

[]-cong : @0 x ≡ y → [ x ] ≡ [ y ]
[]-cong refl = refl
