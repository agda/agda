-- ASR (29 September 2014). Adapted from the example in issue 1269.

-- Case: quote η-reduced and quoteTerm η-reduced.

open import Common.Equality
open import Common.Level
open import Common.Prelude renaming (Nat to ℕ)
open import Common.Product
open import Common.Reflection

data Even  : ℕ → Set where
  isEven0  : Even 0
  isEven+2 : ∀ {n} → Even n → Even (suc (suc n))

pattern expected =
  def (quote ∃)
      ( hArg (def (quote Common.Level.lzero) []) ∷
        hArg (def (quote Common.Level.lzero) []) ∷
        hArg (def (quote ℕ) []) ∷
        vArg (def (quote Even) []) ∷
        [] )

isExpected : Term → Bool
isExpected expected = true
isExpected _        = false

`_ : Bool → Term
` true  = con (quote true) []
` false = con (quote false) []

macro
  checkExpectedType : QName → Tactic
  checkExpectedType i hole =
    bindTC (getType i) λ t →
    give (` isExpected t) hole

input0 : ∃ Even
input0 = 0 , isEven0

input1 : ∃ (λ n → Even n)
input1 = 0 , isEven0

quote0 : Bool
quote0 = checkExpectedType input0

quote1 : Bool
quote1 = checkExpectedType input1

ok0 : quote0 ≡ true
ok0 = refl

ok1 : quote1 ≡ true
ok1 = refl

------------------------------------------------------------------------------
-- For debugging purpose

quotedTerm0 : Term
quotedTerm0 = quoteTerm (∃ Even)

quotedTerm1 : Term
quotedTerm1 = quoteTerm (∃ (λ n → Even n))

b : quotedTerm0 ≡ expected
b = refl

c : quotedTerm1 ≡ expected
c = refl
