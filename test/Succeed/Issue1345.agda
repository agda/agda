-- {-# OPTIONS -v reify:80 #-}

open import Common.Prelude
open import Common.Reflection
open import Common.Equality
open import Agda.Builtin.Sigma

module Issue1345 (A : Set) where

-- Andreas, 2016-07-17
-- Also test correct handling of abstract

abstract
  unquoteDecl idNat = define (vArg idNat)
    (funDef (pi (vArg (def (quote Nat) [])) (abs "" (def (quote Nat) [])))
            (clause (("", vArg unknown) ∷ []) (vArg (var 0) ∷ []) (var 0 []) ∷ []))
  -- This raised the UselessAbstract error in error.
  -- Should work.

abstract
  thm : ∀ n → idNat n ≡ n
  thm n = refl
