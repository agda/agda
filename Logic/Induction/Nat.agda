------------------------------------------------------------------------
-- Various forms of induction for natural numbers
------------------------------------------------------------------------

module Logic.Induction.Nat where

open import Data.Function
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Logic
open import Logic.Induction
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Ordinary induction

Rec : RecStruct ℕ
Rec P zero    = ⊤
Rec P (suc n) = P n

rec-builder : RecursorBuilder Rec
rec-builder P f zero    = tt
rec-builder P f (suc n) = f n (rec-builder P f n)

rec : Recursor Rec
rec = build rec-builder

------------------------------------------------------------------------
-- Complete induction

CRec : RecStruct ℕ
CRec P zero    = ⊤
CRec P (suc n) = P n × CRec P n

cRec-builder : RecursorBuilder CRec
cRec-builder P f zero    = tt
cRec-builder P f (suc n) = f n ih , ih
  where ih = cRec-builder P f n

cRec : Recursor CRec
cRec = build cRec-builder

------------------------------------------------------------------------
-- Complete induction based on <

<-Rec : RecStruct ℕ
<-Rec P n = forall {m} -> m < n -> P m

-- This function makes a case distinction not on zero and suc, but on
-- "anything smaller than n" and n.

max-case
  :  forall {n}
  -> (P : ℕ -> Set)
  -> (forall {m} -> m < n -> P m)
  -> P n
  -> forall {m} -> m ≤ n -> P m
max-case {n = zero}  P lt eq z≤n       = eq
max-case {n = suc n} P lt eq z≤n       = lt (s≤s z≤n)
max-case             P lt eq (s≤s m≤n) =
  max-case (\n -> P (suc n)) (lt ∘ s≤s) eq m≤n

<-rec-builder : RecursorBuilder <-Rec
<-rec-builder P f zero    ()
<-rec-builder P f (suc n) (s≤s m≤n) = max-case P ih (f n ih) m≤n
  where
  ih : <-Rec P n
  ih = <-rec-builder P f n

<-rec : Recursor <-Rec
<-rec = build <-rec-builder
