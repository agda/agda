
open import Common.Prelude
open import Common.Reflection

pattern `Nat = def (quote Nat) []

unquoteDecl x =
  define (hArg x) (funDef `Nat (clause [] [] (quoteTerm 15) ∷ []))
