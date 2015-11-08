
open import Common.Prelude
open import Common.Equality
open import Common.Reflection

pattern vArg a = arg (argInfo visible relevant) a
pattern _`+_ a b = def (quote _+_) (vArg a ∷ vArg b ∷ [])

-- quoteTerm ∘ unquote is normalisation for Term

macro
  -- The unquoted type is also Term → Term.
  eval : Term → Term
  eval u = quote-term (unquote-term u [])

t : Term
t = lam visible (abs "n" (lit (nat 1) `+ var 0 []))

lem : eval t ≡ con (quote suc) []
lem = refl
