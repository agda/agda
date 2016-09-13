
open import Agda.Builtin.Reflection
open import Agda.Builtin.Bool
open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.List

_>>=_ = bindTC

`false `true : Term
`false = con (quote false) []
`true  = con (quote true)  []

macro
  macro? : Name → Term → TC ⊤
  macro? x hole =
    isMacro x >>= λ where
      false → unify hole `false
      true  → unify hole `true

test₁ : macro? macro? ≡ true
test₁ = refl

test₂ : macro? test₁ ≡ false
test₂ = refl

test₃ : macro? true ≡ false
test₃ = refl
