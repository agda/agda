
module _ where

open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool

_>>_ : {A B : Set} → TC A → TC B → TC B
m >> m₁ = m >>= λ _ → m₁

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

macro
  reflectAndCheck : ∀ {a} {A : Set a} → A → Term → TC ⊤
  reflectAndCheck {A = A} x hole = withNormalisation true do
    `x  ← quoteTC x
    `A  ← quoteTC A
    ``x ← checkType `x `A >>= quoteTC
    unify hole ``x

  quoteUnquote : ∀ {a} {A : Set a} → A → Term → TC ⊤
  quoteUnquote x hole = withNormalisation true do
    `x ← quoteTC x
    unify hole `x

module _ (n : Nat) (A : Set) (m : Nat) (j : Fin m) where

  plam₁ : Fin n → Fin m
  plam₁ = λ where zero → j; (suc i) → j

  `plam₁ : Term
  `plam₁ = reflectAndCheck plam₁

  plam₁′ : Fin n → Fin m
  plam₁′ = quoteUnquote plam₁

  refined₁ : n ≡ suc m → Nat
  refined₁ refl = 0
    where
      plam : Fin n → Fin m
      plam = λ where zero → j; (suc i) → i

      `plam : Term
      `plam = reflectAndCheck plam

      plam′ : Fin n → Fin m
      plam′ = quoteUnquote plam

  refined₂ : m ≡ suc n → Nat
  refined₂ refl = 0
    where
      plam : Fin n → Fin m
      plam = λ where zero → j; (suc i) → suc (suc i)

      `plam : Term
      `plam = reflectAndCheck plam

      plam′ : Fin n → Fin m
      plam′ = quoteUnquote plam
