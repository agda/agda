{-# OPTIONS --rewriting --local-confluence-check #-}

open import Agda.Builtin.Equality.Rewrite renaming (primRewriteNoMatch to ⟨_⟩)
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

record Wrap (A : Set) : Set where
  constructor wrap
  field
    unwrap : A
open Wrap

postulate
  f  : Wrap Nat → Nat
  rw₁ : f ⟨ wrap 0 ⟩ ≡ 42
  {-# REWRITE rw₁ #-}

test₁ : f (wrap 0) ≡ 42
test₁ = refl

postulate
  g  : (Nat → Nat) → Nat
  rw₂ : g ⟨ (λ x → x) ⟩ ≡ 42
  {-# REWRITE rw₂ #-}

test₂ : g (λ x → x) ≡ 42
test₂ = refl

postulate
  h   : Nat → Nat
  rw₃ : h (⟨ wrap 0 ⟩ .unwrap) ≡ 42
  {-# REWRITE rw₃ #-}

test₃ : h 0 ≡ 42
test₃ = refl
