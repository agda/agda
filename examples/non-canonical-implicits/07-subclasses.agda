{-# OPTIONS --universe-polymorphism #-}
-- {-# OPTIONS --verbose tc.records.ifs:15 #-}
-- {-# OPTIONS --verbose tc.constr.findInScope:15 #-}
-- {-# OPTIONS --verbose tc.term.args.ifs:15 #-}
-- {-# OPTIONS --verbose cta.record.ifs:15 #-}
-- {-# OPTIONS --verbose tc.section.apply:25 #-}
-- {-# OPTIONS --verbose tc.mod.apply:100 #-}
-- {-# OPTIONS --verbose scope.rec:15 #-}
-- {-# OPTIONS --verbose tc.rec.def:15 #-}

module 07-subclasses where

open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_<_)
open import Relation.Nullary.Decidable
open import Function using (_$_; id)

record Eq (A : Set) : Set where
  field eq : A → A → Bool

primEqBool : Bool → Bool → Bool
primEqBool true = id
primEqBool false = not

eqBool : Eq Bool
eqBool = record { eq = primEqBool }

primEqNat : ℕ → ℕ → Bool
primEqNat a b = ⌊ a ≟ b ⌋

primLtNat : ℕ → ℕ → Bool
primLtNat 0 _ = true
primLtNat (suc a) (suc b) = primLtNat a b
primLtNat _ _ = false

neq : {t : Set} → {{eqT : Eq t}} → t → t → Bool
neq a b = not $ eq a b
  where open module EqWithImplicits {t : Set} {{eqT : Eq t}} = Eq eqT

record Ord₁ (A : Set) : Set where
  field _<_ : A → A → Bool
        eqA : Eq A

ord₁Nat : Ord₁ ℕ
ord₁Nat = record { _<_ = primLtNat; eqA = eqNat }
  where eqNat : Eq ℕ
        eqNat = record { eq = primEqNat }


record Ord₂ {A : Set} (eqA : Eq A) : Set where
  field _<_ : A → A → Bool

ord₂Nat : Ord₂ (record { eq = primEqNat })
ord₂Nat = record { _<_ = primLtNat }


record Ord₃ (A : Set) : Set where
  field _<_ : A → A → Bool
        eqA : Eq A
  open Eq eqA public

ord₃Nat : Ord₃ ℕ
ord₃Nat = record { _<_ = primLtNat; eqA = eqNat }
  where eqNat : Eq ℕ
        eqNat = record { eq = primEqNat }

record Ord₄ {A : Set} (eqA : Eq A) : Set where
  field _<_ : A → A → Bool
  open Eq eqA public

ord₄Nat : Ord₄ (record { eq = primEqNat })
ord₄Nat = record { _<_ = primLtNat }


module test₁ where
  open module Ord₁WithImplicits {t : Set} {{ordT : Ord₁ t}} = Ord₁ ordT
  open module EqWithImplicits {t : Set} {{eqT : Eq t}} = Eq eqT

  eqNat = eqA

  test₁ = 5 < 3
  test₂ = eq 5 3
  test₃ = eq true false
  test₄ : {A : Set} → {{ ordA : Ord₁ A }} → A → A → Bool
  test₄ a b = a < b ∨ eq a b 
    where eqA' = eqA

module test₂ where
  open module Ord₂WithImplicits {t : Set} {eqT : Eq t} {{ordT : Ord₂ eqT}} = Ord₂ ordT
  open module EqWithImplicits {t : Set} {{eqT : Eq t}} = Eq eqT

  eqNat = record { eq = primEqNat }

  test₁ = 5 < 3
  test₂ = eq 5 3
  test₃ = eq true false
  test₄ : {A : Set} → {eqA : Eq A} → {{ ordA : Ord₂ eqA }} → A → A → Bool
  test₄ a b = a < b ∨ eq a b 


module test₃ where
  open module Ord₃WithImplicits {t : Set} {{ordT : Ord₃ t}} = Ord₃ ordT
  open module EqWithImplicits {t : Set} {{eqT : Eq t}} = Eq eqT renaming (eq to eq')

  test₁ = 5 < 3
  test₂ = eq 5 3
  test₃ = eq' true false
  test₄ : {A : Set} → {{ ordA : Ord₃ A }} → A → A → Bool
  test₄ a b = a < b ∨ eq a b 

module test₄ where
  open module Ord₄WithImplicits {t : Set} {eqT : Eq t} {{ordT : Ord₄ eqT}} = Ord₄ ordT
  open module EqWithImplicits {t : Set} {{eqT : Eq t}} = Eq eqT renaming (eq to eq')

  test₁ = 5 < 3
  test₂ = eq 5 3
  test₃ = eq' true false
  test₄ : {A : Set} → {eqA : Eq A} → {{ ordA : Ord₄ eqA }} → A → A → Bool
  test₄ a b = a < b ∨ eq a b 

module test₄′ where
  open module Ord₄WithImplicits {t : Set} {eqT : Eq t} {{ordT : Ord₄ eqT}} = Ord₄ ordT hiding (eq)
  open module EqWithImplicits {t : Set} {{eqT : Eq t}} = Eq eqT

  eqNat = record { eq = primEqNat }

  test₁ = 5 < 3
  test₂ = eq 5 3
  test₃ = eq true false
  test₄ : {A : Set} → {eqA : Eq A} → {{ ordA : Ord₄ eqA }} → A → A → Bool
  test₄ a b = a < b ∨ eq a b 

