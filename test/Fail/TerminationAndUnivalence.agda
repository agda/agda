{- Jesper Cockx, 26-05-2014
   Issue 1023
-}

{-# OPTIONS --cubical-compatible #-}

module TerminationAndUnivalence where

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

J : ∀ {a b} {A : Set a} {x : A} (P : (y : A) → x ≡ y → Set b) →
    (p : P x refl) {y : A} (e : x ≡ y) → P y e
J P p refl = p

data ⊥ : Set where

data WOne : Set where
  wrap : (⊥ → WOne) → WOne

FOne = ⊥ → WOne

f : WOne → FOne
f x ()

g : FOne → WOne
g x = wrap (λ ())

postulate iso : WOne ≡ FOne

noo : (X : Set) → (WOne ≡ X) → X → ⊥
noo .WOne refl (wrap x) = noo FOne iso x

absurd : ⊥
absurd = noo FOne iso (λ ())
