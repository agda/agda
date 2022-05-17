-- Issue #2979 reported by Favonia on 2018-02-23

{-# OPTIONS --cubical-compatible --rewriting --confluence-check #-}

data _==_ {A : Set} (a : A) : A → Set where
  idp : a == a

record Marked (A : Set) : Set where
  constructor mark
  field
    unmark : A
open Marked

postulate
  _↦_ : ∀ {A : Set} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}

postulate
  A : Set
  Q : (I : Marked A → Set) → Set
  q : (I : Marked A → Set) (a : Marked A) → Q I
  Q-elim : (I : Marked A → Set) {P : Q I → Set}
    (q* : (a : Marked A) → P (q I a)) (x : Q I) → P x
  Q-rec : (I : Marked A → Set) {B : Set} (q* : Marked A → B)
    → Q I → B
  Q-rec-β : (I : Marked A → Set) {B : Set} (q* : Marked A → B)
    → (a : Marked A) → Q-rec I {B} q* (q I a) ↦ q* a
{-# REWRITE Q-rec-β #-}

p₀ : Marked A → Set
p₀ (mark a) = A

p₁ : Marked A → Set
p₁ (mark a) = A

q= : ∀ x → Q-rec p₀ (q p₀) x == Q-rec p₁ (q p₁) x
q= = Q-elim p₀ (λ _ → idp)
