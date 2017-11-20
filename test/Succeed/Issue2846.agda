{-# OPTIONS --cubical #-}

open import Agda.Primitive.Cubical

postulate
  Id    : ∀ {ℓ} {A : Set ℓ}     → A    → A    → Set ℓ
  Path  : ∀ {ℓ} {A : Set ℓ}     → A    → A    → Set ℓ
  PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

{-# BUILTIN PATH  Path  #-}
{-# BUILTIN PATHP PathP #-}
{-# BUILTIN ID    Id    #-}
{-# BUILTIN CONID conid #-}

reflPath : ∀ {ℓ} {A : Set ℓ} {x : A} → Path x x
reflPath {x = x} = λ i → x

reflId : ∀ {ℓ} {A : Set ℓ} {x : A} → Id x x
reflId {x = x} = conid i1 reflPath

primitive
 primIdJ : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : ∀ y → Id x y → Set ℓ')
         → P x reflId → {y : A} (p : Id x y) → P y p

Id-comp-Id : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : ∀ y → Id x y → Set ℓ')
           → (b : P x reflId) → Id (primIdJ P b reflId) b
Id-comp-Id P b = reflId

Id-comp-Path : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : ∀ y → Id x y → Set ℓ')
             → (b : P x reflId) → Path (primIdJ P b reflId) b
Id-comp-Path P b = λ i → b
