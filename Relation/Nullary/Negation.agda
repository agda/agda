------------------------------------------------------------------------
-- Properties related to negation
------------------------------------------------------------------------

module Relation.Nullary.Negation where

open import Relation.Nullary
open import Relation.Unary
open import Data.Empty
open import Data.Function
open import Data.Product
open import Category.Monad

contradiction : ∀ {P whatever} → P → ¬ P → whatever
contradiction p ¬p = ⊥-elim (¬p p)

contravariant : ∀ {P Q} → (P → Q) → ¬ Q → ¬ P
contravariant f ¬q p = contradiction (f p) ¬q

-- Note also the following use of flip:

private
  note : ∀ {P Q} → (P → ¬ Q) → Q → ¬ P
  note = flip

------------------------------------------------------------------------
-- Quantifier juggling

∃⟶¬∀¬ : ∀ {A} {P : Pred A} → ∃ P → ¬ (∀ x → ¬ P x)
∃⟶¬∀¬ = flip uncurry

∀⟶¬∃¬ : ∀ {A} {P : Pred A} → (∀ x → P x) → ¬ ∃ λ x → ¬ P x
∀⟶¬∃¬ ∀xPx (x , ¬Px) = ¬Px (∀xPx x)

¬∃⟶∀¬ : ∀ {A} {P : Pred A} → ¬ ∃ (λ x → P x) → ∀ x → ¬ P x
¬∃⟶∀¬ = curry

∀¬⟶¬∃ : ∀ {A} {P : Pred A} → (∀ x → ¬ P x) → ¬ ∃ (λ x → P x)
∀¬⟶¬∃ = uncurry

∃¬⟶¬∀ : ∀ {A} {P : Pred A} → ∃ (λ x → ¬ P x) → ¬ (∀ x → P x)
∃¬⟶¬∀ = flip ∀⟶¬∃¬

------------------------------------------------------------------------
-- Double-negation

¬¬-map : ∀ {P Q} → (P → Q) → ¬ ¬ P → ¬ ¬ Q
¬¬-map f = contravariant (contravariant f)

¬¬-drop : {P : Set} → ¬ ¬ ¬ P → ¬ P
¬¬-drop ¬¬¬P P = ¬¬¬P (λ ¬P → ¬P P)

¬¬-drop-Dec : {P : Set} → Dec P → ¬ ¬ P → P
¬¬-drop-Dec (yes p) ¬¬p = p
¬¬-drop-Dec (no ¬p) ¬¬p = ⊥-elim (¬¬p ¬p)

-- Double-negation is a monad (if we assume that all elements of ¬ ¬ P
-- are equal).

¬¬-Monad : RawMonad (λ P → ¬ ¬ P)
¬¬-Monad = record
  { return = contradiction
  ; _>>=_  = λ x f → ¬¬-drop (¬¬-map f x)
  }

¬¬-push : {P : Set} {Q : P → Set} →
          ¬ ¬ ((x : P) → Q x) → (x : P) → ¬ ¬ Q x
¬¬-push ¬¬P⟶Q P ¬Q = ¬¬P⟶Q (λ P⟶Q → ¬Q (P⟶Q P))

-- A double-negation-translated variant of excluded middle.

excluded-middle : {P : Set} → ¬ ¬ Dec P
excluded-middle ¬h = ¬h (no (λ p → ¬h (yes p)))

-- Call with current continuation in the double-negation monad, or, if
-- you will, a double-negation translation of Peirce's law.

call/cc : ∀ {P whatever} →
          ((P → ¬ ¬ whatever) → ¬ ¬ P) → ¬ ¬ P
call/cc hyp ¬p = hyp (λ p _ → ¬p p) ¬p
