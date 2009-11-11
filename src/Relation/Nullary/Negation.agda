------------------------------------------------------------------------
-- Properties related to negation
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Nullary.Negation where

open import Relation.Nullary
open import Relation.Unary
open import Data.Empty
open import Data.Function
open import Data.Product as Prod
open import Data.Fin
open import Data.Fin.Dec
open import Category.Monad
open import Level

contradiction : ∀ {p w} {P : Set p} {Whatever : Set w} →
                P → ¬ P → Whatever
contradiction p ¬p = ⊥-elim (¬p p)

contraposition : ∀ {p q} {P : Set p} {Q : Set q} →
                 (P → Q) → ¬ Q → ¬ P
contraposition f ¬q p = contradiction (f p) ¬q

-- Note also the following use of flip:

private
  note : ∀ {p q} {P : Set p} {Q : Set q} →
         (P → ¬ Q) → Q → ¬ P
  note = flip

------------------------------------------------------------------------
-- Quantifier juggling

∃⟶¬∀¬ : ∀ {a p} {A : Set a} {P : A → Set p} →
        ∃ P → ¬ (∀ x → ¬ P x)
∃⟶¬∀¬ = flip uncurry

∀⟶¬∃¬ : ∀ {a p} {A : Set a} {P : A → Set p} →
        (∀ x → P x) → ¬ ∃ λ x → ¬ P x
∀⟶¬∃¬ ∀xPx (x , ¬Px) = ¬Px (∀xPx x)

¬∃⟶∀¬ : ∀ {a p} {A : Set a} {P : A → Set p} →
        ¬ ∃ (λ x → P x) → ∀ x → ¬ P x
¬∃⟶∀¬ = curry

∀¬⟶¬∃ : ∀ {a p} {A : Set a} {P : A → Set p} →
        (∀ x → ¬ P x) → ¬ ∃ (λ x → P x)
∀¬⟶¬∃ = uncurry

∃¬⟶¬∀ : ∀ {a p} {A : Set a} {P : A → Set p} →
        ∃ (λ x → ¬ P x) → ¬ (∀ x → P x)
∃¬⟶¬∀ = flip ∀⟶¬∃¬

-- When P is a decidable predicate over a finite set the following
-- lemma can be proved.

¬∀⟶∃¬ : ∀ n {p} (P : Fin n → Set p) → (∀ i → Dec (P i)) →
        ¬ (∀ i → P i) → ∃ λ i → ¬ P i
¬∀⟶∃¬ n P dec ¬P = Prod.map id proj₁ $ ¬∀⟶∃¬-smallest n P dec ¬P

------------------------------------------------------------------------
-- Double-negation

¬¬-map : ∀ {p q} {P : Set p} {Q : Set q} →
         (P → Q) → ¬ ¬ P → ¬ ¬ Q
¬¬-map f = contraposition (contraposition f)

¬¬-drop : ∀ {p} {P : Set p} → ¬ ¬ ¬ P → ¬ P
¬¬-drop ¬¬¬P P = ¬¬¬P (λ ¬P → ¬P P)

¬¬-drop-Dec : ∀ {p} {P : Set p} → Dec P → ¬ ¬ P → P
¬¬-drop-Dec (yes p) ¬¬p = p
¬¬-drop-Dec (no ¬p) ¬¬p = ⊥-elim (¬¬p ¬p)

¬-drop-Dec : ∀ {p} {P : Set p} → Dec (¬ ¬ P) → Dec (¬ P)
¬-drop-Dec (yes ¬¬p) = no ¬¬p
¬-drop-Dec (no ¬¬¬p) = yes (¬¬-drop ¬¬¬p)

-- Double-negation is a monad (if we assume that all elements of ¬ ¬ P
-- are equal).

¬¬-Monad : RawMonad (λ P → ¬ ¬ P)
¬¬-Monad = record
  { return = contradiction
  ; _>>=_  = λ x f → ¬¬-drop (¬¬-map f x)
  }

¬¬-push : ∀ {p q} {P : Set p} {Q : P → Set q} →
          ¬ ¬ ((x : P) → Q x) → (x : P) → ¬ ¬ Q x
¬¬-push ¬¬P⟶Q P ¬Q = ¬¬P⟶Q (λ P⟶Q → ¬Q (P⟶Q P))

-- A double-negation-translated variant of excluded middle (or: every
-- nullary relation is decidable in the double-negation monad).

excluded-middle : ∀ {p} {P : Set p} → ¬ ¬ Dec P
excluded-middle ¬h = ¬h (no (λ p → ¬h (yes p)))

-- If Whatever is instantiated with ¬ ¬ something, then this function
-- is call with current continuation in the double-negation monad, or,
-- if you will, a double-negation translation of Peirce's law.
--
-- In order to prove ¬ ¬ P one can assume ¬ P and prove ⊥. However,
-- sometimes it is nice to avoid leaving the double-negation monad; in
-- that case this function can be used (with Whatever instantiated to
-- ⊥).

call/cc : ∀ {w p} {Whatever : Set w} {P : Set p} →
          ((P → Whatever) → ¬ ¬ P) → ¬ ¬ P
call/cc hyp ¬p = hyp (λ p → ⊥-elim (¬p p)) ¬p
