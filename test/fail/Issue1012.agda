
open import Common.Prelude
open import Common.Reflect

id : {A : Set} → A → A
id x = x

idTerm : Term
idTerm = lam visible (def (quote id) (arg₁ ∷ arg₂ ∷ []))
  where
    arg₁ = arg (arginfo hidden relevant) (def (quote Nat) [])
    arg₂ = arg (arginfo visible relevant) (var 0 [])

-- Should fail since idTerm "λ z → id {Nat} z"
id₂ : {A : Set} → A → A
id₂ = unquote idTerm
