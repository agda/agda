{-# OPTIONS --rewriting --prop #-}

open import Agda.Builtin.Nat

data ⊥ : Prop where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
{-# BUILTIN REWRITE _≡_ #-}

infix 4 _≡_

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

ok : (n : Nat) (p : ⊥) → (n + n) ≡ 0
ok n p = ⊥-elim p

{-# REWRITE ok #-}

notok : (n : Nat) → n + n ≡ 0
notok n = refl

absurd : 2 ≡ 0
absurd = notok 1
