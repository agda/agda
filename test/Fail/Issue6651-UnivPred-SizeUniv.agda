-- Andreas, 2023-05-19, issue #6651

{-# OPTIONS --sized-types #-}
{-# OPTIONS --guarded #-}
-- {-# OPTIONS --level-universe #-}  -- LevelUniv is an alternative to LockUniv
-- {-# OPTIONS --prop #-}  -- with Prop, Agda knows that Set₁ is not invertible

open import Agda.Primitive
open import Agda.Builtin.Size

primitive
  primLockUniv : Set₁

mutual-block : Set₁

Ω : Set₁
Ω = {!!}

Id : (S : Ω) → S → SizeUniv
Id S _ = S

mutual-block = Set

-- Agda 2.6.2.2 and 2.6.3 give an error that is not valid:
--
-- Set != SizeUniv
-- when checking that the expression S has type SizeUniv
--
-- Giving this error means that Agda solved Ω = Set
-- which is not the unique solution if we have one of
-- Prop, LevelUniv or LockUniv.

-- Expect error like this:
--
-- Setω != Set₁
-- when checking that the solution SizeUniv of metavariable _0 has the expected type Set₁
