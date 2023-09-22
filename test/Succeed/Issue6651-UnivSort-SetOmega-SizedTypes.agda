-- Andreas, 2023-05-19, issue #6651
-- Predecessors of Setω if --omega-in-omega and --sized-types

{-# OPTIONS --omega-in-omega #-}  -- or --type-in-type
{-# OPTIONS --sized-types #-}     -- axiom SizeUniv : Setω destroys unicity of solution

open import Agda.Primitive

BEGIN = Set₁
END   = Set

module SetOmega where

  mutual-block : BEGIN

  Ω : Setω
  Ω = _ -- should solve to Setω later

  test : (A : Setω) → A → Ω
  test A _ = A

  mutual-block = END

module SizeUniv where
  open import Agda.Builtin.Size

  mutual-block : BEGIN

  Ω : Setω
  Ω = _ -- should solve to SizeUniv later

  test : (A : SizeUniv) → A → Ω
  test A _ = A

  mutual-block = END
