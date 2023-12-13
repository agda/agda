{-# OPTIONS --rewriting --confluence-check --with-K #-}

open import Agda.Builtin.Equality

{-# BUILTIN REWRITE _≡_ #-}

myrefl : ∀ {ℓ} {A : Set ℓ} {x : A} → x ≡ x
myrefl = ?

UIP : ∀ {ℓ} {A : Set ℓ} {x : A} → myrefl {ℓ} {A} {x} ≡ refl
UIP with refl ← myrefl = refl

{-# REWRITE UIP #-}
