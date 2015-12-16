
open import Common.Prelude
open import Common.Equality
open import Common.Reflection
open import Common.TC

pattern vArg a = arg (argInfo visible relevant) a
pattern _`+_ a b = def (quote _+_) (vArg a ∷ vArg b ∷ [])

-- quoteTerm ∘ unquote is normalisation for Term

macro
  -- The unquoted type is also Term → Tactic.
  eval : Term → Tactic
  eval u = give (quote-term (unquote-term u []))

t : Tactic
t = give (lam visible (abs "n" (lit (nat 1) `+ var 0 [])))

lem : eval t ≡ con (quote suc) []
lem = refl
