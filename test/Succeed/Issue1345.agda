-- {-# OPTIONS -v reify:80 #-}

open import Common.Prelude
open import Common.Reflection
open import Common.TC

module Issue1345 (A : Set) where

unquoteDecl idNat = define idNat (funDef (el unknown (pi (arg (argInfo visible relevant) (el unknown (def (quote Nat) []))) (abs "" (el unknown (def (quote Nat) []))))) (clause (arg (argInfo visible relevant) (var "") ∷ []) (var 0 []) ∷ []))
