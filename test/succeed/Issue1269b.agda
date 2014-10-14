-- ASR (29 September 2014). Adapted from the example in issue 1269.

-- Case: quote η-reduced and non η-reduced.

open import Common.Equality
open import Common.Level
open import Common.Prelude renaming (Nat to ℕ)
open import Common.Product
open import Common.Reflection

data Even  : ℕ → Set where
  isEven0  : Even 0
  isEven+2 : ∀ {n} → Even n → Even (suc (suc n))

input0 : ∃ Even
input0 = 0 , isEven0

quote0 : Term
quote0 with type (quote input0)
quote0 | el s t = t

input1 : ∃ (λ n → Even n)
input1 = 0 , isEven0

quote1 : Term
quote1 with type (quote input1)
quote1 | el s t = t

ok : quote0 ≡ quote1
ok = refl

------------------------------------------------------------------------------
-- For debugging purpose

a : quote0 ≡
    def (quote Σ)
        ( arg (argInfo hidden relevant) (def (quote Common.Level.lzero) []) ∷
          arg (argInfo hidden relevant) (def (quote Common.Level.lzero) []) ∷
          arg (argInfo visible relevant) (def (quote ℕ) []) ∷
          arg (argInfo visible relevant) (def (quote Even) []) ∷
          []
        )
a = refl

b : quote1 ≡
    def (quote Σ)
        ( arg (argInfo hidden relevant) (def (quote Common.Level.lzero) []) ∷
          arg (argInfo hidden relevant) (def (quote Common.Level.lzero) []) ∷
          arg (argInfo visible relevant) (def (quote ℕ) []) ∷
          arg (argInfo visible relevant) (def (quote Even) []) ∷
          []
        )
b = refl
