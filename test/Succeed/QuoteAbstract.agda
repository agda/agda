-- Andreas, 2025-04-29, PR #7828
-- In droppedPars, AbstractDefn isn't __IMPOSSIBLE__

open import Agda.Builtin.Equality
open import Agda.Builtin.Reflection

macro
  doQuote : ∀ {ℓ} {A : Set ℓ} → A → Term → TC _
  doQuote x hole = bindTC (quoteTC x) (λ qx → bindTC (quoteTC qx) (unify hole))

abstract
  A : Set₁
  A = Set

testQuote₁ : doQuote A ≡ doQuote A
testQuote₁ = refl

-- Used to trigger internal error with PR #7828.
-- Should succeed.
