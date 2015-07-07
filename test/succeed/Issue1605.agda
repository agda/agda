-- Andreas, 2015-07-07 Let _ pattern be instantiable by an inaccessible pattern

module _ where

open import Common.Equality

-- These used to work and should still work:

transV1 : ∀{A : Set} (a b c : A) → a ≡ b → b ≡ c → a ≡ c
transV1 _ ._ ._ refl refl = refl

transV2 : ∀{A : Set} (a b c : A) → a ≡ b → b ≡ c → a ≡ c
transV2 ._ _ ._ refl refl = refl

transV3 : ∀{A : Set} (a b c : A) → a ≡ b → b ≡ c → a ≡ c
transV3 ._ ._ _ refl refl = refl

transH : ∀{A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
transH refl refl = refl

transH1 : ∀{A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
transH1 {a = _}{b = ._}{c = ._} refl refl = refl

transH1' : ∀{A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
transH1' {a = _} refl refl = refl

-- NEW: the following should also work:

transVNew : ∀{A : Set} (a b c : A) → a ≡ b → b ≡ c → a ≡ c
transVNew _ _ _ refl refl = refl

transHNew : ∀{A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
transHNew {a = _}{b = _}{c = _} refl refl = refl
