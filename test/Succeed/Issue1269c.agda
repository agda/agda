-- ASR (30 September 2014). Adapted from the example in issue 1269.

-- Case: quoteTerm η-reduced and non η-reduced.

open import Common.Equality
open import Common.Level
open import Common.Prelude renaming (Nat to ℕ)
open import Common.Product
open import Common.Reflection

data Even  : ℕ → Set where
  isEven0  : Even 0
  isEven+2 : ∀ {n} → Even n → Even (suc (suc n))

quotedTerm0 : Term
quotedTerm0 = quoteTerm (∃ Even)

quotedTerm1 : Term
quotedTerm1 = quoteTerm (∃ (λ n → Even n))

ok : quotedTerm0 ≡ quotedTerm1
ok = refl

------------------------------------------------------------------------------
-- For debugging purpose

a : quotedTerm0 ≡
    def (quote Σ)
        ( arg (argInfo hidden relevant) (def (quote Common.Level.lzero) []) ∷
          arg (argInfo hidden relevant) (def (quote Common.Level.lzero) []) ∷
          arg (argInfo visible relevant) (def (quote ℕ) []) ∷
          arg (argInfo visible relevant) (def (quote Even) []) ∷
          []
        )
a = refl

b : quotedTerm1 ≡
    def (quote Σ)
        ( arg (argInfo hidden relevant) (def (quote Common.Level.lzero) []) ∷
          arg (argInfo hidden relevant) (def (quote Common.Level.lzero) []) ∷
          arg (argInfo visible relevant) (def (quote ℕ) []) ∷
          arg (argInfo visible relevant) (def (quote Even) []) ∷
          []
        )
b = refl
