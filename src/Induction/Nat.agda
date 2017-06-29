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

<′-Rec : ∀ {ℓ} → RecStruct ℕ ℓ ℓ
<′-Rec = WfRec _<′_

mutual

  <′-well-founded : Well-founded _<′_
  <′-well-founded n = acc (<′-well-founded′ n)

  <′-well-founded′ : ∀ n → <′-Rec (Acc _<′_) n
  <′-well-founded′ zero     _ ()
  <′-well-founded′ (suc n) .n ≤′-refl       = <′-well-founded n
  <′-well-founded′ (suc n)  m (≤′-step m<n) = <′-well-founded′ n m m<n

module _ {ℓ} where
  open WF.All <′-well-founded ℓ public
    renaming ( wfRec-builder to <′-rec-builder
             ; wfRec to <′-rec
             )

------------------------------------------------------------------------
-- Complete induction based on _<_

<-Rec : ∀ {ℓ} → RecStruct ℕ ℓ ℓ
<-Rec = WfRec _<_

<-well-founded : Well-founded _<_
<-well-founded = Subrelation.well-founded ≤⇒≤′ <′-well-founded

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
≺-well-founded = Subrelation.well-founded ≺⇒<′ <′-well-founded

module _ {ℓ} where
  open WF.All ≺-well-founded ℓ public
    renaming ( wfRec-builder to ≺-rec-builder
             ; wfRec to ≺-rec
             )

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

    cRec (λ _ → ℕ) half₁-step (2 + n)                                     ≡⟨⟩

    half₁-step (2 + n) (cRec-builder (λ _ → ℕ) half₁-step (2 + n))        ≡⟨⟩

    half₁-step (2 + n)
      (let ih = cRec-builder (λ _ → ℕ) half₁-step (1 + n) in
       half₁-step (1 + n) ih , ih)                                        ≡⟨⟩

    half₁-step (2 + n)
      (let ih = cRec-builder (λ _ → ℕ) half₁-step n in
       half₁-step (1 + n) (half₁-step n ih , ih) , half₁-step n ih , ih)  ≡⟨⟩

    1 + half₁-step n (cRec-builder (λ _ → ℕ) half₁-step n)                ≡⟨⟩

    1 + cRec (λ _ → ℕ) half₁-step n                                       ≡⟨⟩

    1 + half₁ n                                                           ∎

    where open ≡-Reasoning

  -- The application half₂ (2 + n) is definitionally equal to
  -- 1 + half₂ n. Perhaps it is instructive to see why.

  half₂-2+ : ∀ n → half₂ (2 + n) ≡ 1 + half₂ n
  half₂-2+ n = begin

    half₂ (2 + n)                                                         ≡⟨⟩

    <′-rec (λ _ → ℕ) half₂-step (2 + n)                                   ≡⟨⟩

    half₂-step (2 + n) (<′-rec-builder (λ _ → ℕ) half₂-step (2 + n))      ≡⟨⟩

    1 + <′-rec-builder (λ _ → ℕ) half₂-step (2 + n) n (≤′-step ≤′-refl)   ≡⟨⟩

    1 + Some.wfRec-builder (λ _ → ℕ) half₂-step (2 + n)
          (<′-well-founded (2 + n)) n (≤′-step ≤′-refl)                   ≡⟨⟩

    1 + Some.wfRec-builder (λ _ → ℕ) half₂-step (2 + n)
          (acc (<′-well-founded′ (2 + n))) n (≤′-step ≤′-refl)            ≡⟨⟩

    1 + half₂-step n
          (Some.wfRec-builder (λ _ → ℕ) half₂-step n
             (<′-well-founded′ (2 + n) n (≤′-step ≤′-refl)))              ≡⟨⟩

    1 + half₂-step n
          (Some.wfRec-builder (λ _ → ℕ) half₂-step n
             (<′-well-founded′ (1 + n) n ≤′-refl))                        ≡⟨⟩

    1 + half₂-step n
          (Some.wfRec-builder (λ _ → ℕ) half₂-step n (<′-well-founded n)) ≡⟨⟩

    1 + half₂-step n (<′-rec-builder (λ _ → ℕ) half₂-step n)              ≡⟨⟩

    1 + <′-rec (λ _ → ℕ) half₂-step n                                     ≡⟨⟩

    1 + half₂ n                                                           ∎

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
  -- <-rec.

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
