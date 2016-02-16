
open import Common.Prelude
open import Common.Reflection

id : {A : Set} → A → A
id x = x

idTerm : Term
idTerm = lam visible (abs "x" (def (quote id) (arg₁ ∷ arg₂ ∷ [])))
  where
    arg₁ = arg (argInfo hidden relevant) (def (quote Nat) [])
    arg₂ = arg (argInfo visible relevant) (var 0 [])

-- Should fail since idTerm "λ z → id {Nat} z"
id₂ : {A : Set} → A → A
id₂ = unquote (give idTerm)
