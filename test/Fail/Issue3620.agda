{-# OPTIONS --cubical --safe #-}
module _ where

open import Agda.Primitive
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Glue
open import Agda.Builtin.Bool


-- If primGlue does not reduce away we should report an error for
-- patterns of other types.
--
-- In the future we might want to allow the constructor glue itself as
-- a pattern.
test : ∀ φ → primGlue {ℓ' = lzero} Bool {φ = φ} ? ? → Bool
test _ true = ?
test _ false = ?
