{-# OPTIONS --prop --rewriting --confluence-check #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

{-# BUILTIN REWRITE _≡_ #-}

data _≐_ {ℓ} {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≐ x

postulate
  subst : ∀ {ℓ ℓ′} {A : Set ℓ} (P : A → Set ℓ′)
        → (x y : A) → x ≐ y → P x → P y
  subst-rew : ∀ {ℓ ℓ′} {A : Set ℓ} (P : A → Set ℓ′)
            → {x : A} (e : x ≐ x) (p : P x) → subst P x x e p ≡ p
{-# REWRITE subst-rew #-}

data Box (A : Prop) : Set where
  box : A -> Box A

foo : (A : Prop)(x y : A)(P : Box A → Set)(p : P (box x)) → subst P (box x) (box y) refl p ≐ p
foo A x y P p = refl -- refl does not type check
