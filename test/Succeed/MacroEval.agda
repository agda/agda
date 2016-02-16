
open import Common.Prelude
open import Common.Equality
open import Common.Reflection

pattern _`+_ a b = def (quote _+_) (vArg a ∷ vArg b ∷ [])

`_ : Term → Term
` con c [] = con (quote Term.con) (vArg (lit (qname c)) ∷ vArg (con (quote []) []) ∷ [])
` _        = unknown

-- Prevent quotation
data WrapTerm : Set where
  wrap : Term → WrapTerm

macro
  eval : WrapTerm → Tactic
  eval (wrap u) hole = bindTC (normalise u) λ u → unify hole (` u)

t : Term
t = lam visible (abs "n" (lit (nat 1) `+ var 0 []))

lem : eval (wrap t) ≡ Term.con (quote suc) []
lem = refl
