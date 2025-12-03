{-# OPTIONS --rewriting --without-K #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Unit
open import Agda.Primitive

module Issue5929 where

variable
  A B : Set
  x y : A

subst : ∀ (P : A → Set) → x ≡ y → P x → P y
subst P refl p = p

PathOver : (P : A → Set) → x ≡ y → P x → P y → Set
PathOver P refl x y = x ≡ y

syntax PathOver P p x y = x ≡[ P ↓ p ]≡ y

dcong : ∀ {B : A → Set} (f : (x : A) → B x) (p : x ≡ y) → f x ≡[ B ↓ p ]≡ f y
dcong f refl = refl

postulate
  Circle : Set
  base   : Circle
  loop   : base ≡ base

  circle-elim : ∀ (P : Circle → Set) (baseᴾ : P base)
              → baseᴾ ≡[ P ↓ loop ]≡ baseᴾ
              → ∀ x → P x

  circle-elim-base : ∀ (P : Circle → Set) (baseᴾ : P base)
                      (loopᴾ : baseᴾ ≡[ P ↓ loop ]≡ baseᴾ)
                  → circle-elim P baseᴾ loopᴾ base ≡ baseᴾ
  {-# REWRITE circle-elim-base #-}

  circle-elim-loop : ∀ (P : Circle → Set) (baseᴾ : P base)
                      (loopᴾ : baseᴾ ≡[ P ↓ loop ]≡ baseᴾ)
                  → dcong (circle-elim P baseᴾ loopᴾ) loop ≡ loopᴾ
  {-# REWRITE circle-elim-loop #-}


-- Subject reduction failure can be witnessed with:

{-
helper : (f g : Circle → B) (fg : f ≡ g)
       → subst (λ □ → □ base ≡[ (λ _ → B) ↓ loop ]≡ □ base)
               fg (dcong f loop)
       ≡ dcong g loop
helper f g refl = refl

module _ (p q : tt ≡[ (λ _ → ⊤) ↓ loop ]≡ tt) where

  pq : p ≡ q
  pq = helper (circle-elim (λ _ → ⊤) tt p) (circle-elim (λ _ → ⊤) tt q) refl

  pq-is-refl : pq ≡ {!!}
  -- If we normalise the goal, we see that |pq| reduces to |refl|, but this does
  -- not typecheck!
  pq-is-refl = {!!}
-}
