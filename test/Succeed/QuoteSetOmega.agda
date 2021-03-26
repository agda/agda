open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Reflection

testQuote : quoteTerm Setω ≡ agda-sort (inf 0)
testQuote = refl

macro
  doUnquote : Term → Term → TC _
  doUnquote t hole = bindTC (unquoteTC t) (unify hole)

testUnquote : doUnquote (agda-sort (inf 0))
testUnquote = ∀ ℓ → Set ℓ
