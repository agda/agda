module Issue1362 where

open import Common.Prelude
open import Common.Equality
open import Common.Reflection

module M₁ (A₁ : Set) where

  data D (B : Set) : Set where

  type₁ : TC Type
  type₁ = getType (quote D)

module M₂ (A₂ : Set) where

  open M₁ A₂

  type₂ : TC Type
  type₂ = getType (quote D)

open M₁ Nat
open M₂ Nat

foo : type₁ ≡ type₂
foo = cong getType {quote D} {quote D} ?
