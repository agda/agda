{-# OPTIONS -v treeless.opt:20 #-}

module _ where

open import Common.Prelude
open import Common.Equality

data Dec {a} (A : Set a) : Set a where
  yes : A → Dec A
  no  : (A → ⊥) → Dec A

decEq₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {f : A → B → C} →
           (∀ {x y z w} → f x y ≡ f z w → x ≡ z) →
           (∀ {x y z w} → f x y ≡ f z w → y ≡ w) →
           ∀ {x y z w} → Dec (x ≡ y) → Dec (z ≡ w) → Dec (f x z ≡ f y w)
decEq₂ f-inj₁ f-inj₂ (no neq)    _         = no λ eq → neq (f-inj₁ eq)
decEq₂ f-inj₁ f-inj₂  _         (no neq)   = no λ eq → neq (f-inj₂ eq)
decEq₂ f-inj₁ f-inj₂ (yes refl) (yes refl) = yes refl

main : IO Unit
main = putStrLn ""
