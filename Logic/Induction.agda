------------------------------------------------------------------------
-- An abstraction of various forms of recursion/induction
------------------------------------------------------------------------

module Logic.Induction where

-- A RecStruct describes the allowed structure of recursion. The
-- examples below should explain what this is all about.

RecStruct : Set -> Set1
RecStruct a = (a -> Set) -> (a -> Set)

-- A recursor builder constructs a recursion structure for a given
-- input.

RecursorBuilder : forall {a} -> RecStruct a -> Set1
RecursorBuilder {a} Rec =
     (P : a -> Set)
  -> (forall x -> Rec P x -> P x)
  -> forall x -> Rec P x

-- A recursor can be used to actually compute/prove something useful.

Recursor : forall {a} -> RecStruct a -> Set1
Recursor {a} Rec =
     (P : a -> Set)
  -> (forall x -> Rec P x -> P x)
  -> forall x -> P x

-- And recursors can be constructed from recursor builders.

build
  :  forall {a} {Rec : RecStruct a}
  -> RecursorBuilder Rec
  -> Recursor Rec
build builder P f x = f x (builder P f x)

------------------------------------------------------------------------
-- Example: Ordinary induction for natural numbers

open import Data.Nat
open import Data.Unit
open import Data.Product

ℕ-Rec : RecStruct ℕ
ℕ-Rec P zero    = ⊤
ℕ-Rec P (suc n) = P n

ℕ-rec-builder : RecursorBuilder ℕ-Rec
ℕ-rec-builder P f zero    = tt
ℕ-rec-builder P f (suc n) = f n (ℕ-rec-builder P f n)

ℕ-rec : Recursor ℕ-Rec
ℕ-rec = build ℕ-rec-builder

------------------------------------------------------------------------
-- Example: Complete induction for natural numbers

ℕ-CRec : RecStruct ℕ
ℕ-CRec P zero    = ⊤
ℕ-CRec P (suc n) = P n × ℕ-CRec P n

ℕ-cRec-builder : RecursorBuilder ℕ-CRec
ℕ-cRec-builder P f zero    = tt
ℕ-cRec-builder P f (suc n) = f n ih , ih
  where ih = ℕ-cRec-builder P f n

ℕ-cRec : Recursor ℕ-CRec
ℕ-cRec = build ℕ-cRec-builder
