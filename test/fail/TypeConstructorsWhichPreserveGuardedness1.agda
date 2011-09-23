-- Note that the flag --guardedness-preserving-type-constructors is
-- not (should not be) enabled in this module.

module TypeConstructorsWhichPreserveGuardedness1 where

open import Imports.Coinduction

record ⊤ : Set where

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

record ∃ {A : Set} (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

data Rec (A : ∞ Set) : Set where
  fold : ♭ A → Rec A

module ℕ₁ where

  ℕ : Set
  ℕ = ⊤ ⊎ Rec (♯ ℕ)

  zero : ℕ
  zero = inj₁ _

  suc : ℕ → ℕ
  suc n = inj₂ (fold n)

  ℕ-rec : (P : ℕ → Set) →
          P zero →
          (∀ n → P n → P (suc n)) →
          ∀ n → P n
  ℕ-rec P z s (inj₁ _)        = z
  ℕ-rec P z s (inj₂ (fold n)) = s n (ℕ-rec P z s n)

module ℕ₂ where

  data ℕC : Set where
    ′zero : ℕC
    ′suc  : ℕC

  mutual

    ℕ : Set
    ℕ = ∃ λ (c : ℕC) → ℕ′ c

    ℕ′ : ℕC → Set
    ℕ′ ′zero = ⊤
    ℕ′ ′suc  = Rec (♯ ℕ)

  zero : ℕ
  zero = (′zero , _)

  suc : ℕ → ℕ
  suc n = (′suc , fold n)

  ℕ-rec : (P : ℕ → Set) →
          P zero →
          (∀ n → P n → P (suc n)) →
          ∀ n → P n
  ℕ-rec P z s (′zero , _)      = z
  ℕ-rec P z s (′suc  , fold n) = s n (ℕ-rec P z s n)
