{-# OPTIONS --cubical-compatible #-}

module ExtLamDefp where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

f : ∀ {A : Set} {x y : A} → x ≡ y → x ≡ y
f = λ { refl → refl }

_ : f {Nat} {0} {0} ≡ (λ x → x)
_ = refl
