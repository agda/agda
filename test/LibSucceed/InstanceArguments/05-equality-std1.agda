{-# OPTIONS --universe-polymorphism #-}
-- {-# OPTIONS --verbose tc.records.ifs:15 #-}
-- {-# OPTIONS --verbose tc.constr.findInScope:15 #-}
-- {-# OPTIONS --verbose tc.term.args.ifs:15 #-}

module InstanceArguments.05-equality-std1 where

open import Relation.Binary.PropositionalEquality hiding (decSetoid; isDecEquivalence)
open import Relation.Nullary
open import Relation.Binary using (IsDecEquivalence; module IsDecEquivalence; Reflexive; module DecSetoid)
open import Data.Bool using (false; true)
open import Data.Bool.Properties using (≡-decSetoid)
open DecSetoid ≡-decSetoid using (isDecEquivalence)

open module IsDecEquivalenceWithImplicits = IsDecEquivalence {{...}} using (_≟_)

instance boolInstance = isDecEquivalence

test : Dec (false ≡ true)
test = false ≟ true

test2 : ∀ {a ℓ} {A : Set a} {_≈_} → {{ide : IsDecEquivalence {a} {ℓ} {A} _≈_}} →
        Reflexive _≈_
test2 = IsDecEquivalenceWithImplicits.refl

