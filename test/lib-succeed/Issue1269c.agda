-- ASR (30 September 2014). Adapted from the example in issue 1269.

-- Case: quoteTerm η-reduced and non η-reduced.

open import Data.Nat
open import Data.List
open import Data.Product
open import Reflection
open import Relation.Binary.PropositionalEquality

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
        ( arg (arg-info hidden relevant) unknown ∷
          arg (arg-info hidden relevant) unknown ∷
          arg (arg-info visible relevant) (def (quote ℕ) []) ∷
          arg (arg-info visible relevant) (def (quote Even) []) ∷
          []
        )
a = refl

b : quotedTerm1 ≡
    def (quote Σ)
        ( arg (arg-info hidden relevant) unknown ∷
          arg (arg-info hidden relevant) unknown ∷
          arg (arg-info visible relevant) (def (quote ℕ) []) ∷
          arg (arg-info visible relevant) (def (quote Even) []) ∷
          []
        )
b = refl
