{-# OPTIONS --erasure --allow-unsolved-metas #-}

open import Agda.Builtin.Equality

postulate @0 A : Set

@0 f : (X : Set) → A ≡ X → Set
f X refl = {!!}

sym : ∀ {ℓ} {X : Set ℓ} {x y : X} → x ≡ y → y ≡ x
sym refl = refl

@0 g : (X : Set) → A ≡ X → Set
g X eq with (sym eq)
... | refl = {!!}
