------------------------------------------------------------------------
-- One form of induction for natural numbers
------------------------------------------------------------------------

-- I want universe polymorphism.

module Induction1.Nat where

open import Data.Nat
import Induction1.WellFounded as WF

------------------------------------------------------------------------
-- Complete induction based on <′

open WF _<′_ using (Acc; acc)

allAcc : ∀ n → Acc n
allAcc n = acc (helper n)
  where
  helper : ∀ n m → m <′ n → Acc m
  helper zero     _ ()
  helper (suc n) .n ≤′-refl        = acc (helper n)
  helper (suc n)  m (≤′-step m<′n) = helper n m m<′n

open WF _<′_ public using () renaming (WfRec to <-Rec)
open WF.All _<′_ allAcc public
  renaming ( wfRec-builder to <-rec-builder
           ; wfRec to <-rec
           )
