------------------------------------------------------------------------
-- The Agda standard library
--
-- Various forms of induction for natural numbers
------------------------------------------------------------------------

module Induction.Nat where

open import Function
open import Data.Nat
open import Data.Fin
open import Data.Fin.Props
open import Data.Product
open import Data.Unit
open import Induction
open import Induction.WellFounded as WF
open import Level using (Lift)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

------------------------------------------------------------------------
-- Ordinary induction

Rec : ∀ ℓ → RecStruct ℕ ℓ ℓ
Rec _ P zero    = Lift ⊤
Rec _ P (suc n) = P n

rec-builder : ∀ {ℓ} → RecursorBuilder (Rec ℓ)
rec-builder P f zero    = _
rec-builder P f (suc n) = f n (rec-builder P f n)

rec : ∀ {ℓ} → Recursor (Rec ℓ)
rec = build rec-builder

------------------------------------------------------------------------
-- Complete induction

CRec : ∀ ℓ → RecStruct ℕ ℓ ℓ
CRec _ P zero    = Lift ⊤
CRec _ P (suc n) = P n × CRec _ P n

cRec-builder : ∀ {ℓ} → RecursorBuilder (CRec ℓ)
cRec-builder P f zero    = _
cRec-builder P f (suc n) = f n ih , ih
  where ih = cRec-builder P f n

cRec : ∀ {ℓ} → Recursor (CRec ℓ)
cRec = build cRec-builder

------------------------------------------------------------------------
-- Complete induction based on _<′_

<-Rec : ∀ {ℓ} → RecStruct ℕ ℓ ℓ
<-Rec = WfRec _<′_

mutual

  <-well-founded : Well-founded _<′_
  <-well-founded n = acc (<-well-founded′ n)

  <-well-founded′ : ∀ n → <-Rec (Acc _<′_) n
  <-well-founded′ zero     _ ()
  <-well-founded′ (suc n) .n ≤′-refl       = <-well-founded n
  <-well-founded′ (suc n)  m (≤′-step m<n) = <-well-founded′ n m m<n

module _ {ℓ} where
  open WF.All <-well-founded ℓ public
    renaming ( wfRec-builder to <-rec-builder
             ; wfRec to <-rec
             )

------------------------------------------------------------------------
-- Complete induction based on _≺_

≺-Rec : ∀ {ℓ} → RecStruct ℕ ℓ ℓ
≺-Rec = WfRec _≺_

≺-well-founded : Well-founded _≺_
≺-well-founded = Subrelation.well-founded ≺⇒<′ <-well-founded

module _ {ℓ} where
  open WF.All ≺-well-founded ℓ public
    renaming ( wfRec-builder to ≺-rec-builder
             ; wfRec to ≺-rec
             )

------------------------------------------------------------------------
-- Examples

private

 module Examples where

  -- The half function.

  half₁ : ℕ → ℕ
  half₁ = cRec _ λ
    { zero          _                → zero
    ; (suc zero)    _                → zero
    ; (suc (suc n)) (_ , half₁n , _) → suc half₁n
    }

  half₂ : ℕ → ℕ
  half₂ = <-rec _ λ
    { zero          _   → zero
    ; (suc zero)    _   → zero
    ; (suc (suc n)) rec → suc (rec n (≤′-step ≤′-refl))
    }
