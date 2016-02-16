-- {-# OPTIONS -v reify:80 #-}

open import Common.Prelude
open import Common.Reflection
open import Common.Equality

module Issue1345 (A : Set) where

unquoteDecl idNat = define (vArg idNat)
  (funDef (pi (vArg (def (quote Nat) [])) (abs "" (def (quote Nat) [])))
          (clause (vArg (var "") ∷ []) (var 0 []) ∷ []))

thm : ∀ n → idNat n ≡ n
thm n = refl
