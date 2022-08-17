{-# OPTIONS --cubical #-}

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Id

reflPath : ∀ {ℓ} {A : Set ℓ} {x : A} → x ≡ x
reflPath {x = x} = λ i → x

reflId' : ∀ {ℓ} {A : Set ℓ} {x : A} → Id x x
reflId' {x = x} = conid i1 reflPath

_ : ∀ {ℓ} {A : Set ℓ} {x : A} → reflId' {x = x} ≡ reflId
_ = reflPath

Id-comp-Id : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : ∀ y → Id x y → Set ℓ')
           → (b : P x reflId) → Id (IdJ P b reflId) b
Id-comp-Id P b = reflId

Id-comp-Path : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : ∀ y → Id x y → Set ℓ')
             → (b : P x reflId) → (IdJ P b reflId) ≡ b
Id-comp-Path P b = λ i → b
