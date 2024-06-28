{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

postulate
  +-identityʳ : (m : Nat) → m + zero ≡ m
  +-suc : (m n : Nat) → m + suc n ≡ suc (m + n)
  +-suc-suc : ∀ (m n : Nat) → suc m + suc n ≡ suc (suc (m + n))

{-# REWRITE +-identityʳ +-suc +-suc-suc #-}
