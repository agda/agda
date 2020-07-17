
module QuoteTerm where

open import Common.Reflection
open import Common.Prelude renaming (Nat to ℕ; module Nat to ℕ)

data _≡_ {a}{A : Set a}(x : A) : A → Set where
  refl : x ≡ x

test₁ : quoteTerm (λ {A : Set} (x : A) → x)
         ≡ lam hidden (abs "A" (lam visible (abs "x" (var 0 []))))
test₁ = refl

-- Local variables are de Bruijn indices, do not forget to shift
test₂ : (λ {A : Set} (x : A) → quoteTerm x) ≡ (λ x → var 0 [])
test₂ = refl

-- Terms are not normalized before being unquoted
test₃ : quoteTerm (1 + 1) ≡ lit (nat 2) → ⊥
test₃ ()

syntax id A x = x ∶ A
id : (A : Set) → A → A
id A x = x

-- _∶_ from the Function module can help in case of ambiguities
test₄ : quoteTerm (zero ∶ ℕ) ≡
        def (quote id)
            (vArg (def (quote ℕ) []) ∷
             vArg (con (quote zero) []) ∷
             [])
test₄ = refl

-- Andreas, 2020-06-05, issue #4734
-- Test that primShowQName prints something reasonable
-- for quoted names.

issue4734 : primShowQName (quote ℕ) ≡ "Agda.Builtin.Nat.Nat"
issue4734 = refl

-- Not sure this response is very reasonable, since
-- it suggest a qualified name that does not exist.
