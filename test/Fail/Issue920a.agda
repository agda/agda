-- Andreas, 2013-10-26, reported by Jesper Cockx

{-# OPTIONS --cubical-compatible #-}

module Issue920a where

import Common.Level
open import Common.Equality

record ⊥ : Set where

data Bool : Set where
  true false : Bool

-- Standard eliminator for ≡
J : ∀ {a b} {A : Set a} {x : A} {Φ : (y : A) → x ≡ y → Set b} →
            Φ x refl → {y : A} → (e : x ≡ y) → Φ y e
J φ refl = φ

-- A kind of heterogeneous equality
_≃_ : {A : Set} (x : A) {A' : Set} → A' → Set _
_≃_ {A} x {A'} x' = (E : A ≡ A') → J x E ≡ x'

-- It shouldn't be possible to define this without K
≃refl : {A : Set} {x : A} → x ≃ x
≃refl {x = x} = λ E → J {Φ = λ A' E' → J x E' ≡ _} refl E

-- These can be given using univalence
postulate Swap : Bool ≡ Bool
postulate swap : true ≡ J {Φ = λ A _ → A} false Swap

-- Univalence and ≃refl don't play nice together
right : (true ≡ false) → ⊥
right ()

wrong : true ≡ false
wrong = trans swap (≃refl Swap)

madness : ⊥
madness = right wrong
