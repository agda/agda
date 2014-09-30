-- ASR (29 September 2014). Adapted from the example in issue 1269.

-- Case: quote η-reduced and quoteTerm η-reduced.

open import Data.Nat
open import Data.List
open import Data.Product
open import Reflection
open import Relation.Binary.PropositionalEquality

data Even  : ℕ → Set where
  isEven0  : Even 0
  isEven+2 : ∀ {n} → Even n → Even (suc (suc n))

input0 : ∃ Even
input0 = 0 , isEven0

quote0 : Term
quote0 with type (quote input0)
quote0 | el s t = t

quotedTerm0 : Term
quotedTerm0 = quoteTerm (∃ Even)

ok : quote0 ≡ quotedTerm0
ok = refl

------------------------------------------------------------------------------
-- For debugging purpose

a : quote0 ≡
    def (quote Σ)
        ( arg (arg-info hidden relevant) unknown ∷
          arg (arg-info hidden relevant) unknown ∷
          arg (arg-info visible relevant) (def (quote ℕ) []) ∷
          arg (arg-info visible relevant) (def (quote Even) []) ∷
          []
        )
a = refl

b : quotedTerm0 ≡
    def (quote Σ)
        ( arg (arg-info hidden relevant) unknown ∷
          arg (arg-info hidden relevant) unknown ∷
          arg (arg-info visible relevant) (def (quote ℕ) []) ∷
          arg (arg-info visible relevant) (def (quote Even) []) ∷
          []
        )
b = refl
