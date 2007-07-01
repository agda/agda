------------------------------------------------------------------------
-- An abstraction of various forms of recursion/induction
------------------------------------------------------------------------

module Logic.Induction where

-- Recursion predicates. The examples below should explain what this
-- is all about. See also Logic.Induction.Lexicographic.

RecPred : Set -> Set1
RecPred a = (a -> Set) -> (a -> Set)

-- Recursor builders build elements of recursion predicates.

RecursorBuilder : forall {a} -> RecPred a -> Set1
RecursorBuilder {a} Rec =
     (P : a -> Set)
  -> (forall x -> Rec P x -> P x)
  -> forall x -> Rec P x

-- A recursor can be used to actually compute/prove something useful.

Recursor : forall {a} -> RecPred a -> Set1
Recursor {a} Rec =
     (P : a -> Set)
  -> (forall x -> Rec P x -> P x)
  -> forall x -> P x

-- And recursors can be constructed from recursor builders.

build
  :  forall {a} {Rec : RecPred a}
  -> RecursorBuilder Rec
  -> Recursor Rec
build builder P f x = f x (builder P f x)

------------------------------------------------------------------------
-- Example: Ordinary induction for natural numbers

open import Data.Nat
open import Data.Unit
open import Data.Product

ℕ-Rec : RecPred ℕ
ℕ-Rec P zero    = ⊤
ℕ-Rec P (suc n) = P n

ℕ-rec-builder : RecursorBuilder ℕ-Rec
ℕ-rec-builder P f zero    = tt
ℕ-rec-builder P f (suc n) = f n (ℕ-rec-builder P f n)

ℕ-rec : Recursor ℕ-Rec
ℕ-rec = build ℕ-rec-builder

------------------------------------------------------------------------
-- Example: Complete induction for natural numbers

ℕ-CRec : RecPred ℕ
ℕ-CRec P zero    = ⊤
ℕ-CRec P (suc n) = P n × ℕ-CRec P n

ℕ-crec-builder : RecursorBuilder ℕ-CRec
ℕ-crec-builder P f zero    = tt
ℕ-crec-builder P f (suc n) = f n ih , ih
  where ih = ℕ-crec-builder P f n

ℕ-crec : Recursor ℕ-CRec
ℕ-crec = build ℕ-crec-builder
