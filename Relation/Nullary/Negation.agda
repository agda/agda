------------------------------------------------------------------------
-- Properties related to negation
------------------------------------------------------------------------

module Relation.Nullary.Negation where

open import Relation.Nullary
open import Relation.Unary
open import Data.Empty
open import Data.Function
open import Data.Product as Prod
open import Data.Fin
open import Data.Fin.Dec
open import Category.Monad

contradiction : ∀ {P whatever} → P → ¬ P → whatever
contradiction p ¬p = ⊥-elim (¬p p)

contraposition : ∀ {P Q} → (P → Q) → ¬ Q → ¬ P
contraposition f ¬q p = contradiction (f p) ¬q

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

-- When P is a decidable predicate over a finite set the following
-- lemma can be proved.

¬∀⟶∃¬ : ∀ n (P : Pred (Fin n)) → (∀ i → Dec (P i)) →
        ¬ (∀ i → P i) → ∃ λ i → ¬ P i
¬∀⟶∃¬ n P dec ¬P = Prod.map id proj₁ $ ¬∀⟶∃¬-smallest n P dec ¬P

------------------------------------------------------------------------
-- Double-negation

¬¬-map : ∀ {P Q} → (P → Q) → ¬ ¬ P → ¬ ¬ Q
¬¬-map f = contraposition (contraposition f)

¬¬-drop : {P : Set} → ¬ ¬ ¬ P → ¬ P
¬¬-drop ¬¬¬P P = ¬¬¬P (λ ¬P → ¬P P)

¬¬-drop-Dec : {P : Set} → Dec P → ¬ ¬ P → P
¬¬-drop-Dec (yes p) ¬¬p = p
¬¬-drop-Dec (no ¬p) ¬¬p = ⊥-elim (¬¬p ¬p)

¬-drop-Dec : {P : Set} → Dec (¬ ¬ P) → Dec (¬ P)
¬-drop-Dec (yes ¬¬p) = no ¬¬p
¬-drop-Dec (no ¬¬¬p) = yes (¬¬-drop ¬¬¬p)

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

-- A double-negation-translated variant of excluded middle (or: every
-- nullary relation is decidable in the double-negation monad).

excluded-middle : {P : Set} → ¬ ¬ Dec P
excluded-middle ¬h = ¬h (no (λ p → ¬h (yes p)))

-- If whatever is instantiated with ¬ ¬ something, then this function
-- is call with current continuation in the double-negation monad, or,
-- if you will, a double-negation translation of Peirce's law.
--
-- In order to prove ¬ ¬ P one can assume ¬ P and prove ⊥. However, it
-- is sometimes nice to avoid leaving the double-negation monad; in
-- that case this function can be used (with whatever instantiated to
-- ⊥).

call/cc : ∀ {whatever P : Set} → ((P → whatever) → ¬ ¬ P) → ¬ ¬ P
call/cc hyp ¬p = hyp (λ p → ⊥-elim (¬p p)) ¬p
