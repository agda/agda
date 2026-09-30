{-# OPTIONS --keep-pattern-variables #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

test₁ : (m : Nat) → m ≡ 0 → Set
test₁ m eq = {!eq!}

test₂ : (A B : Set) → A ≡ B → Set
test₂ A B eq = {!eq!}
