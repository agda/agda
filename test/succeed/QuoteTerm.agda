
module QuoteTerm where

open import Common.Reflect
open import Common.Prelude renaming (Nat to ℕ)

data _≡_ {a}{A : Set a}(x : A) : A → Set where
  refl : x ≡ x

test₁ : quoteTerm (λ {A : Set} (x : A) → x)
         ≡ lam hidden (lam visible (var 0 []))
test₁ = refl

-- Local variables are de Bruijn indices, do not forget to shift
test₂ : (λ {A : Set} (x : A) → quoteTerm x) ≡ (λ x → var 0 [])
test₂ = refl

-- Terms are normalized before being unquoted
test₃ : quoteTerm (0 + 0) ≡ con (quote zero) []
test₃ = refl

syntax id A x = x ∶ A
id : (A : Set) → A → A
id A x = x

-- _∶_ from the Function module can help in case of ambiguities
test₄ : quoteTerm (zero ∶ ℕ) ≡ con (quote ℕ.zero) []
test₄ = refl
