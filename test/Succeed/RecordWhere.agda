open import Common.Prelude
open import Common.Equality

record Empty : Set where

ε : Empty
ε = record where

module M where
  proj₁ = 3
  distraction = false

module WithAccessorsInScope where
  open import Common.Product

  pair₁ : Nat × Nat
  pair₁ = record where
    proj₁ = 4
    proj₂ = 2

  eq₁ : pair₁ ≡ (4 , 2)
  eq₁ = refl

  pair₂ : Nat × Nat
  pair₂ = record where
    proj₂ = 7
    proj₁ = proj₂ + 3
    distraction = false

  eq₂ : pair₂ ≡ (10 , 7)
  eq₂ = refl

  pair₃ : (Nat → Nat) × Nat
  pair₃ = record where
    proj₁ x = x + 1
    proj₂ = 10

  eq₃․₁ : proj₁ pair₃ 1 ≡ 2
  eq₃․₁ = refl

  eq₃․₂ : proj₂ pair₃ ≡ 10
  eq₃․₂ = refl

  pair₄ : Nat × Nat
  pair₄ = record where
    open M using (proj₁; distraction)
    proj₂ = 5

  eq₄ : pair₄ ≡ (3 , 5)
  eq₄ = refl

  pair₅ : Nat × Nat
  pair₅ = record where
    open M using () renaming (proj₁ to proj₂)
    proj₁ = 5

  eq₅ : pair₅ ≡ (5 , 3)
  eq₅ = refl

  pair₆ : Nat × Nat
  pair₆ = record where
    open Σ pair₅ using (proj₁)
    proj₂ = pair₅ .proj₂ + 1

  eq₆ : pair₆ ≡ (5 , 4)
  eq₆ = refl

  pair₇ : Nat × Nat
  pair₇ = record where
    proj₁ = pair₅ .proj₂ + 1
    open Σ pair₅ using () renaming (proj₁ to proj₂)

  eq₇ : pair₇ ≡ (4 , 5)
  eq₇ = refl

  pair₈ : Nat × Nat
  pair₈ = record where
    proj₂ , proj₁ = pair₇

  eq₈ : pair₈ ≡ (5 , 4)
  eq₈ = refl

  pair₉ : Nat × Nat
  pair₉ = record where
    _ , proj₁ = pair₇
    proj₂ = 9

  eq₉ : pair₉ ≡ (5 , 9)
  eq₉ = refl

  pair₁₀ : Nat × Nat
  pair₁₀ = record where
    record { proj₁ = proj₂ ; proj₂ = proj₁ } = pair₇

  eq₁₀ : pair₁₀ ≡ (5 , 4)
  eq₁₀ = refl

module WithoutAccessorsInScope where
  open import Common.Product hiding (proj₁; proj₂)

  pair₁ : Nat × Nat
  pair₁ = record where
    proj₁ = 4
    proj₂ = 2

  eq₁ : pair₁ ≡ (4 , 2)
  eq₁ = refl

  pair₂ : Nat × Nat
  pair₂ = record where
    proj₂ = 7
    proj₁ = proj₂ + 3
    distraction = false

  eq₂ : pair₂ ≡ (10 , 7)
  eq₂ = refl

  pair₃ : (Nat → Nat) × Nat
  pair₃ = record where
    proj₁ x = x + 1
    proj₂ = 10

  eq₃․₁ : Σ.proj₁ pair₃ 1 ≡ 2
  eq₃․₁ = refl

  eq₃․₂ : Σ.proj₂ pair₃ ≡ 10
  eq₃․₂ = refl

  pair₄ : Nat × Nat
  pair₄ = record where
    open M using (proj₁; distraction)
    proj₂ = 5

  eq₄ : pair₄ ≡ (3 , 5)
  eq₄ = refl

  pair₅ : Nat × Nat
  pair₅ = record where
    open M using () renaming (proj₁ to proj₂)
    proj₁ = 5

  eq₅ : pair₅ ≡ (5 , 3)
  eq₅ = refl

  pair₆ : Nat × Nat
  pair₆ = record where
    open Σ pair₅ using (proj₁)
    proj₂ = pair₅ .Σ.proj₂ + 1

  eq₆ : pair₆ ≡ (5 , 4)
  eq₆ = refl

  pair₇ : Nat × Nat
  pair₇ = record where
    proj₁ = pair₅ .Σ.proj₂ + 1
    open Σ pair₅ using () renaming (proj₁ to proj₂)

  eq₇ : pair₇ ≡ (4 , 5)
  eq₇ = refl

  pair₈ : Nat × Nat
  pair₈ = record where
    proj₂ , proj₁ = pair₇

  eq₈ : pair₈ ≡ (5 , 4)
  eq₈ = refl

  pair₉ : Nat × Nat
  pair₉ = record where
    _ , proj₁ = pair₇
    proj₂ = 9

  eq₉ : pair₉ ≡ (5 , 9)
  eq₉ = refl

  pair₁₀ : Nat × Nat
  pair₁₀ = record where
    record { proj₁ = proj₂ ; proj₂ = proj₁ } = pair₇

  eq₁₀ : pair₁₀ ≡ (5 , 4)
  eq₁₀ = refl
