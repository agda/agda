-- Andreas, 2023-05-19, issue #6651
-- With --type-in-type or --omega-in-omega and without --prop,
-- Setω has exactly one canonical precedessor.
-- Setω₁ has exactly one canonical precedessor always without --prop.

{-# OPTIONS --omega-in-omega #-}
{-# OPTIONS --two-level #-}

open import Agda.Primitive

BEGIN = Set₁
END   = Set

module SetOmega where

  mutual-block : BEGIN

  Ω : Setω
  Ω = _ -- can only be Setω (or equivalent)

  id : (A : Ω) → A → A
  id A x = x

  mutual-block = END

module SetOmega1 where

  mutual-block : BEGIN

  Ω : Setω₁
  Ω = _ -- can only be Setω (or equivalent)

  id : (A : Ω) → A → A
  id A x = x

  mutual-block = END

module SSetOmega where

  mutual-block : BEGIN

  Ω : SSetω
  Ω = _ -- can only be SSetω (or equivalent)

  id : (A : Ω) → A → A
  id A x = x

  mutual-block = END

module SSetOmega1 where

  mutual-block : BEGIN

  Ω : SSetω₁
  Ω = _ -- can only be SSetω (or equivalent)

  id : (A : Ω) → A → A
  id A x = x

  mutual-block = END
