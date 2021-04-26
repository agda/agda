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

pattern hid = argInfo hidden relevant
pattern vis = argInfo visible relevant

pattern expected-eta =
  def (quote ∃)
      ( arg hid (def (quote Common.Level.lzero) []) ∷
        arg hid (def (quote Common.Level.lzero) []) ∷
        arg hid (def (quote ℕ) []) ∷
        arg vis (def (quote Even) []) ∷
        [] )

pattern expected-noeta =
  def (quote ∃)
      ( arg hid (def (quote Common.Level.lzero) []) ∷
        arg hid (def (quote Common.Level.lzero) []) ∷
        arg hid (def (quote ℕ) []) ∷
        arg vis (lam visible (abs "n" (def (quote Even) (arg vis (var 0 []) ∷ [])))) ∷
        [] )

isEta : Term → Bool
isEta expected-eta = true
isEta _            = false

isNoEta : Term → Bool
isNoEta expected-noeta = true
isNoEta _              = false

`_ : Bool → Term
` true  = con (quote true) []
` false = con (quote false) []

macro
  checkExpectedType : (Term → Bool) → QName → Tactic
  checkExpectedType isExpected i hole =
    bindTC (getType i) λ t →
    give (` isExpected t) hole

input0 : ∃ Even
input0 = 0 , isEven0

input1 : ∃ (λ n → Even n)
input1 = 0 , isEven0

quote0 : Bool
quote0 = checkExpectedType isEta input0

quote1 : Bool
quote1 = checkExpectedType isNoEta input1

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

b : quotedTerm0 ≡ expected-eta
b = refl

c : quotedTerm1 ≡ expected-noeta
c = refl
