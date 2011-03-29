{-# OPTIONS --universe-polymorphism #-}
-- {-# OPTIONS --verbose tc.records.ifs:15 #-}
-- {-# OPTIONS --verbose tc.constr.findInScope:15 #-}
-- {-# OPTIONS --verbose tc.term.args.ifs:15 #-}
-- {-# OPTIONS --verbose cta.record.ifs:15 #-}
-- {-# OPTIONS --verbose tc.section.apply:25 #-}
-- {-# OPTIONS --verbose tc.mod.apply:100 #-}
-- {-# OPTIONS --verbose scope.rec:15 #-}
-- {-# OPTIONS --verbose tc.rec.def:15 #-}

module 04-equality where

import Data.Empty as E
open import Function using (_$_)

data Bool : Set where
  true : Bool
  false : Bool

or : Bool → Bool → Bool
or true _ = true
or _ true = true
or false false = false

and : Bool → Bool → Bool
and false _ = false
and _ false = false
and true true = false

not : Bool → Bool
not true = false
not false = true

id : {A : Set} → A → A
id v = v

primEqBool : Bool → Bool → Bool
primEqBool true = id
primEqBool false = not

record Eq (A : Set) : Set where
  field eq : A → A → Bool
module WithImplicits' {A} {{eqA : Eq A}} = Eq eqA using (eq)


eqBool : Eq Bool
eqBool = record { eq = primEqBool }

-- eq : {t : Set} → {{eqT : Eq t}} → t → t → Bool
-- eq {{eqT}} = Eq.eq eqT
open EqWithImplicits


-- test2 : ∀ {a ℓ} {A : Set a} {_≈_} → {{ide : IsDecEquivalence {a} {ℓ} {A} _≈_}} → Reflexive _≈_
-- test2 {a} {ℓ} {A} {_≈_} {{ide}} = IsDecEquivalence.WithImplicits.refl {a} {ℓ} {A} {_≈_} {{ide}}

neq : {t : Set} → {{eqT : Eq t}} → t → t → Bool
neq a b = not $ eq a b

test = eq false false

