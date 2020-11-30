module _ where

open import Common.Prelude hiding (_>>=_)
open import Common.Reflection
open import Common.Equality
open import Agda.Builtin.Sigma

module _ (A : Set) where
  record R : Set where

  `R₀ : Type
  `R₀ = def (quote R) []

  `R₁ : Term → Type
  `R₁ a = def (quote R) (vArg a ∷ [])

  `Nat : Type
  `Nat = def (quote Nat) []

  _`→_ : Type → Type → Type
  a `→ b = pi (vArg a) (abs "x" b)

  helper-type₀ : Type
  helper-type₀ = `R₀ `→ `R₀

  helper-type₁ : Type
  helper-type₁ = `R₁ `Nat `→ `R₁ `Nat

  helper-term : Term
  helper-term = var 0 []

  helper-telescope : List (Σ String λ _ → Arg Type)
  helper-telescope = ("x" , vArg unknown) ∷ []

  helper-patterns : List (Arg Pattern)
  helper-patterns = vArg (var 0) ∷
                    []

  defineHelper : Type → TC ⊤
  defineHelper t =
    freshName "n" >>= λ n →
    declareDef (vArg n) t >>= λ _ →
    defineFun n (clause helper-telescope helper-patterns helper-term ∷ [])

  noFail : TC ⊤ → TC Bool
  noFail m = catchTC (bindTC m λ _ → returnTC true) (returnTC false)

  mac : Type → Tactic
  mac t hole =
    noFail (defineHelper t) >>= λ b →
    quoteTC b >>= unify hole

  macro
    mac₀ : Tactic
    mac₀ = mac helper-type₀

    mac₁ : Tactic
    mac₁ = mac helper-type₁

  within-module-succeeds₀ : mac₀ ≡ true
  within-module-succeeds₀ = refl

  within-module-fails₁ : mac₁ ≡ false
  within-module-fails₁ = refl

outside-module-fails₀ : mac₀ Nat ≡ false
outside-module-fails₀ = refl

outside-module-succeeds₁ : mac₁ Nat ≡ true
outside-module-succeeds₁ = refl
