
module _ where

open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Reflection

record R : Set₁ where
  field
    N : Set
    s : N → N
open R

macro
  nf : Name → Term → TC ⊤
  nf x hole = bindTC (normalise (def x [])) (unify hole)

  q : R → Term → TC ⊤
  q r hole = bindTC (quoteTC r) (unify hole)

r : R
r = λ where .N → ⊤; .s x → x

-- These looped

r₁ : R
r₁ = nf r

r₂ : R
r₂ = q (λ where .N → ⊤; .s x → x)
