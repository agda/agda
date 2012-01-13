-- Andreas, 2012-01-13
module Issue555a where

-- Do we want to allow this?
data Exp : Set → Set1
data Exp Γ where -- needs to report that too many parameters are given
  var : Exp Γ
  bla : {Δ : Set} → Exp Δ → Exp (Δ → Γ) → Exp Γ

-- A declared index is turned into a parameter by the definition.



