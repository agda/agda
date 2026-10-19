{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

record SomeLevel {ℓ} (A : Set ℓ) : Setω where
  field
    level : Level

open SomeLevel ⦃...⦄ public

record Semigroup {ℓ} (A : Set ℓ) : Set ℓ where
  field _◇_ : A → A → A

open Semigroup ⦃...⦄ public

module _ {ℓ} (A : Set ℓ) ⦃ _ : Semigroup A ⦄ where
  record Comm ⦃ l : SomeLevel A ⦄ : Set (ℓ ⊔ level) where
    field ◇-comm  : ∀ (x y : A) → (x ◇ y) ≡ (y ◇ x)

  someLevel : SomeLevel A
  someLevel .level = ℓ

  Comm' : Set ℓ
  Comm' = Comm
                   ⦃ someLevel ⦄ -- fails in master
                   -- ⦃ record { level = ℓ } ⦄ -- succeeds in master

open Comm ⦃...⦄ public

module _ {ℓ} {A : Set ℓ} ⦃ _ : Semigroup A ⦄ ⦃ a : Comm' A ⦄ where

  open Comm ⦃ l = record { level = ℓ } ⦄ a public
    renaming (◇-comm to ◇-comm≡)

module _ {a b} {A : Set a} {b : Set b} {B : Set} ⦃ m : Semigroup A ⦄ ⦃ n : Semigroup B ⦄ where

  Semigroup-× : Semigroup (Σ A λ _ → B)
  Semigroup-× ._◇_ (a , b) (a′ , b′) = (a ◇ a′ , b ◇ b′)

  open Semigroup Semigroup-× renaming (_◇_ to _◇×_)

  Comm-× : ⦃ Comm' A ⦄ → ⦃ Comm' B ⦄
                  → ∀ x y → (x ◇× y) ≡ (y ◇× x)
  Comm-× (a , b) (c , d)
    with (a ◇ c) | ◇-comm≡ a c
  ... | _ | p = {!!}
