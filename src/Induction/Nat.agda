------------------------------------------------------------------------
-- The Agda standard library
--
-- Various forms of induction for natural numbers
------------------------------------------------------------------------

module Induction.Nat where

open import Function
open import Data.Nat
open import Data.Nat.Properties using (≤⇒≤′)
open import Data.Fin using (_≺_)
open import Data.Fin.Properties
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

recBuilder : ∀ {ℓ} → RecursorBuilder (Rec ℓ)
recBuilder P f zero    = _
recBuilder P f (suc n) = f n (recBuilder P f n)

rec : ∀ {ℓ} → Recursor (Rec ℓ)
rec = build recBuilder

------------------------------------------------------------------------
-- Complete induction

CRec : ∀ ℓ → RecStruct ℕ ℓ ℓ
CRec _ P zero    = Lift ⊤
CRec _ P (suc n) = P n × CRec _ P n

cRecBuilder : ∀ {ℓ} → RecursorBuilder (CRec ℓ)
cRecBuilder P f zero    = _
cRecBuilder P f (suc n) = f n ih , ih
  where ih = cRecBuilder P f n

cRec : ∀ {ℓ} → Recursor (CRec ℓ)
cRec = build cRecBuilder

------------------------------------------------------------------------
-- Complete induction based on _<′_

<′-Rec : ∀ {ℓ} → RecStruct ℕ ℓ ℓ
<′-Rec = WfRec _<′_

mutual

  <′-wellFounded : WellFounded _<′_
  <′-wellFounded n = acc (<′-wellFounded′ n)

  <′-wellFounded′ : ∀ n → <′-Rec (Acc _<′_) n
  <′-wellFounded′ zero     _ ()
  <′-wellFounded′ (suc n) .n ≤′-refl       = <′-wellFounded n
  <′-wellFounded′ (suc n)  m (≤′-step m<n) = <′-wellFounded′ n m m<n

module _ {ℓ} where
  open WF.All <′-wellFounded ℓ public
    renaming ( wfRecBuilder to <′-recBuilder
             ; wfRec        to <′-rec
             )
    hiding (wfRec-builder)

------------------------------------------------------------------------
-- Complete induction based on _<_

<-Rec : ∀ {ℓ} → RecStruct ℕ ℓ ℓ
<-Rec = WfRec _<_

<-wellFounded : WellFounded _<_
<-wellFounded = Subrelation.wellFounded ≤⇒≤′ <′-wellFounded

module _ {ℓ} where
  open WF.All <-wellFounded ℓ public
    renaming ( wfRecBuilder to <-recBuilder
             ; wfRec        to <-rec
             )
    hiding (wfRec-builder)

------------------------------------------------------------------------
-- Complete induction based on _≺_

≺-Rec : ∀ {ℓ} → RecStruct ℕ ℓ ℓ
≺-Rec = WfRec _≺_

≺-wellFounded : WellFounded _≺_
≺-wellFounded = Subrelation.wellFounded ≺⇒<′ <′-wellFounded

module _ {ℓ} where
  open WF.All ≺-wellFounded ℓ public
    renaming ( wfRecBuilder to ≺-recBuilder
             ; wfRec        to ≺-rec
             )
    hiding (wfRec-builder)

------------------------------------------------------------------------
-- Examples

private

 module Examples where

  -- Doubles its input.

  twice : ℕ → ℕ
  twice = rec _ λ
    { zero    _       → zero
    ; (suc n) twice-n → suc (suc twice-n)
    }

  -- Halves its input (rounding downwards).
  --
  -- The step function is mentioned in a proof below, so it has been
  -- given a name. (The mutual keyword is used to avoid having to give
  -- a type signature for the step function.)

  mutual

    half₁-step = λ
      { zero          _                → zero
      ; (suc zero)    _                → zero
      ; (suc (suc n)) (_ , half₁n , _) → suc half₁n
      }

    half₁ : ℕ → ℕ
    half₁ = cRec _ half₁-step

  -- An alternative implementation of half₁.

  mutual

    half₂-step = λ
      { zero          _   → zero
      ; (suc zero)    _   → zero
      ; (suc (suc n)) rec → suc (rec n (≤′-step ≤′-refl))
      }

    half₂ : ℕ → ℕ
    half₂ = <′-rec _ half₂-step

  -- The application half₁ (2 + n) is definitionally equal to
  -- 1 + half₁ n. Perhaps it is instructive to see why.

  half₁-2+ : ∀ n → half₁ (2 + n) ≡ 1 + half₁ n
  half₁-2+ n = begin

    half₁ (2 + n)                                                         ≡⟨⟩

    cRec _ half₁-step (2 + n)                                             ≡⟨⟩

    half₁-step (2 + n) (cRecBuilder _ half₁-step (2 + n))                 ≡⟨⟩

    half₁-step (2 + n)
      (let ih = cRecBuilder _ half₁-step (1 + n) in
       half₁-step (1 + n) ih , ih)                                        ≡⟨⟩

    half₁-step (2 + n)
      (let ih = cRecBuilder _ half₁-step n in
       half₁-step (1 + n) (half₁-step n ih , ih) , half₁-step n ih , ih)  ≡⟨⟩

    1 + half₁-step n (cRecBuilder _ half₁-step n)                         ≡⟨⟩

    1 + cRec _ half₁-step n                                               ≡⟨⟩

    1 + half₁ n                                                           ∎

    where open ≡-Reasoning

  -- The application half₂ (2 + n) is definitionally equal to
  -- 1 + half₂ n. Perhaps it is instructive to see why.

  half₂-2+ : ∀ n → half₂ (2 + n) ≡ 1 + half₂ n
  half₂-2+ n = begin

    half₂ (2 + n)                                               ≡⟨⟩

    <′-rec _ half₂-step (2 + n)                                 ≡⟨⟩

    half₂-step (2 + n) (<′-recBuilder _ half₂-step (2 + n))     ≡⟨⟩

    1 + <′-recBuilder _ half₂-step (2 + n) n (≤′-step ≤′-refl)  ≡⟨⟩

    1 + Some.wfRecBuilder _ half₂-step (2 + n)
          (<′-wellFounded (2 + n)) n (≤′-step ≤′-refl)          ≡⟨⟩

    1 + Some.wfRecBuilder _ half₂-step (2 + n)
          (acc (<′-wellFounded′ (2 + n))) n (≤′-step ≤′-refl)   ≡⟨⟩

    1 + half₂-step n
          (Some.wfRecBuilder _ half₂-step n
             (<′-wellFounded′ (2 + n) n (≤′-step ≤′-refl)))     ≡⟨⟩

    1 + half₂-step n
          (Some.wfRecBuilder _ half₂-step n
             (<′-wellFounded′ (1 + n) n ≤′-refl))               ≡⟨⟩

    1 + half₂-step n
          (Some.wfRecBuilder _ half₂-step n (<′-wellFounded n)) ≡⟨⟩

    1 + half₂-step n (<′-recBuilder _ half₂-step n)             ≡⟨⟩

    1 + <′-rec _ half₂-step n                                   ≡⟨⟩

    1 + half₂ n                                                 ∎

    where open ≡-Reasoning

  -- Some properties that the functions above satisfy, proved using
  -- cRec.

  half₁-+₁ : ∀ n → half₁ (twice n) ≡ n
  half₁-+₁ = cRec _ λ
    { zero          _                        → refl
    ; (suc zero)    _                        → refl
    ; (suc (suc n)) (_ , half₁twice-n≡n , _) →
        cong (suc ∘ suc) half₁twice-n≡n
    }

  half₂-+₁ : ∀ n → half₂ (twice n) ≡ n
  half₂-+₁ = cRec _ λ
    { zero          _                        → refl
    ; (suc zero)    _                        → refl
    ; (suc (suc n)) (_ , half₁twice-n≡n , _) →
        cong (suc ∘ suc) half₁twice-n≡n
    }

  -- Some properties that the functions above satisfy, proved using
  -- <′-rec.

  half₁-+₂ : ∀ n → half₁ (twice n) ≡ n
  half₁-+₂ = <′-rec _ λ
    { zero          _   → refl
    ; (suc zero)    _   → refl
    ; (suc (suc n)) rec →
        cong (suc ∘ suc) (rec n (≤′-step ≤′-refl))
    }

  half₂-+₂ : ∀ n → half₂ (twice n) ≡ n
  half₂-+₂ = <′-rec _ λ
    { zero          _   → refl
    ; (suc zero)    _   → refl
    ; (suc (suc n)) rec →
        cong (suc ∘ suc) (rec n (≤′-step ≤′-refl))
    }

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

rec-builder      = recBuilder
cRec-builder     = cRecBuilder
<′-rec-builder   = <′-recBuilder
<-rec-builder    = <-recBuilder
≺-rec-builder    = ≺-recBuilder
<′-well-founded  = <′-wellFounded
<′-well-founded′ = <′-wellFounded′
<-well-founded   = <-wellFounded
≺-well-founded   = ≺-wellFounded
