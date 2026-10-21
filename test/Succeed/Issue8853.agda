{-# OPTIONS --cubical --safe #-}
module Issue8853 where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Cubical.Path using (_≡_)

f : (p : tt ≡ tt) → tt ≡ tt
f p i = p i

macro
  checkBody : Term → TC ⊤
  checkBody hole =
    bindTC (withReconstructed true (getDefinition (quote f))) λ where
      (function (clause _ _ (var _ (_ ∷ [])) ∷ [])) →
        unify hole (con (quote tt) [])
      _ → typeError (strErr "Unexpected reconstructed body" ∷ [])

testBody : ⊤
testBody = checkBody
