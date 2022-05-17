{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Reflection

macro
  doQuote : ∀ {ℓ} {A : Set ℓ} → A → Term → TC _
  doQuote x hole = bindTC (quoteTC x) (λ qx → bindTC (quoteTC qx) (unify hole))

testQuote₁ : doQuote Prop ≡ agda-sort (propLit 0)
testQuote₁ = refl

testQuote₂ : ∀ {ℓ} → doQuote (Prop ℓ) ≡ agda-sort (prop (var 0 []))
testQuote₂ = refl

macro
  doUnquote : Term → Term → TC _
  doUnquote t hole = bindTC (unquoteTC t) (unify hole)

testUnquote₁ : doUnquote (agda-sort (propLit 0)) ≡ Prop
testUnquote₁ = refl

testUnquote₂ : ∀ {ℓ} → doUnquote (agda-sort (prop (var 0 []))) ≡ Prop ℓ
testUnquote₂ = refl
