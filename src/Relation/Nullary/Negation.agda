------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to negation
------------------------------------------------------------------------

module Relation.Nullary.Negation where

open import Relation.Nullary
open import Relation.Unary
open import Data.Bool.Base using (Bool; false; true; if_then_else_)
open import Data.Empty
open import Function
open import Data.Product as Prod
open import Data.Sum as Sum
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

-- If we can decide P, then we can decide its negation.

¬? : ∀ {p} {P : Set p} → Dec P → Dec (¬ P)
¬? (yes p) = no (λ ¬p → ¬p p)
¬? (no ¬p) = yes ¬p

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

------------------------------------------------------------------------
-- Double-negation

¬¬-map : ∀ {p q} {P : Set p} {Q : Set q} →
         (P → Q) → ¬ ¬ P → ¬ ¬ Q
¬¬-map f = contraposition (contraposition f)

-- Stability under double-negation.

Stable : ∀ {ℓ} → Set ℓ → Set ℓ
Stable P = ¬ ¬ P → P

-- Everything is stable in the double-negation monad.

stable : ∀ {p} {P : Set p} → ¬ ¬ Stable P
stable ¬[¬¬p→p] = ¬[¬¬p→p] (λ ¬¬p → ⊥-elim (¬¬p (¬[¬¬p→p] ∘ const)))

-- Negated predicates are stable.

negated-stable : ∀ {p} {P : Set p} → Stable (¬ P)
negated-stable ¬¬¬P P = ¬¬¬P (λ ¬P → ¬P P)

-- Decidable predicates are stable.

decidable-stable : ∀ {p} {P : Set p} → Dec P → Stable P
decidable-stable (yes p) ¬¬p = p
decidable-stable (no ¬p) ¬¬p = ⊥-elim (¬¬p ¬p)

¬-drop-Dec : ∀ {p} {P : Set p} → Dec (¬ ¬ P) → Dec (¬ P)
¬-drop-Dec (yes ¬¬p) = no ¬¬p
¬-drop-Dec (no ¬¬¬p) = yes (negated-stable ¬¬¬p)

-- Double-negation is a monad (if we assume that all elements of ¬ ¬ P
-- are equal).

¬¬-Monad : ∀ {p} → RawMonad (λ (P : Set p) → ¬ ¬ P)
¬¬-Monad = record
  { return = contradiction
  ; _>>=_  = λ x f → negated-stable (¬¬-map f x)
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

-- The "independence of premise" rule, in the double-negation monad.
-- It is assumed that the index set (Q) is inhabited.

independence-of-premise
  : ∀ {p q r} {P : Set p} {Q : Set q} {R : Q → Set r} →
    Q → (P → Σ Q R) → ¬ ¬ (Σ[ x ∈ Q ] (P → R x))
independence-of-premise {P = P} q f = ¬¬-map helper excluded-middle
  where
  helper : Dec P → _
  helper (yes p) = Prod.map id const (f p)
  helper (no ¬p) = (q , ⊥-elim ∘′ ¬p)

-- The independence of premise rule for binary sums.

independence-of-premise-⊎
  : ∀ {p q r} {P : Set p} {Q : Set q} {R : Set r} →
    (P → Q ⊎ R) → ¬ ¬ ((P → Q) ⊎ (P → R))
independence-of-premise-⊎ {P = P} f = ¬¬-map helper excluded-middle
  where
  helper : Dec P → _
  helper (yes p) = Sum.map const const (f p)
  helper (no ¬p) = inj₁ (⊥-elim ∘′ ¬p)

private

  -- Note that independence-of-premise-⊎ is a consequence of
  -- independence-of-premise (for simplicity it is assumed that Q and
  -- R have the same type here):

  corollary : ∀ {p ℓ} {P : Set p} {Q R : Set ℓ} →
              (P → Q ⊎ R) → ¬ ¬ ((P → Q) ⊎ (P → R))
  corollary {P = P} {Q} {R} f =
    ¬¬-map helper (independence-of-premise
                     true ([ _,_ true , _,_ false ] ∘′ f))
    where
    helper : ∃ (λ b → P → if b then Q else R) → (P → Q) ⊎ (P → R)
    helper (true  , f) = inj₁ f
    helper (false , f) = inj₂ f

-- The classical statements of excluded middle and double-negation
-- elimination.

Excluded-Middle : (ℓ : Level) → Set (suc ℓ)
Excluded-Middle p = {P : Set p} → Dec P

Double-Negation-Elimination : (ℓ : Level) → Set (suc ℓ)
Double-Negation-Elimination p = {P : Set p} → Stable P

private

  -- The two statements above are equivalent. The proofs are so
  -- simple, given the definitions above, that they are not exported.

  em⇒dne : ∀ {ℓ} → Excluded-Middle ℓ → Double-Negation-Elimination ℓ
  em⇒dne em = decidable-stable em

  dne⇒em : ∀ {ℓ} → Double-Negation-Elimination ℓ → Excluded-Middle ℓ
  dne⇒em dne = dne excluded-middle
