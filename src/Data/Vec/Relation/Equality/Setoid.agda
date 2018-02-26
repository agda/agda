------------------------------------------------------------------------
-- The Agda standard library
--
-- Semi-heterogeneous vector equality over setoids
------------------------------------------------------------------------

open import Relation.Binary

module Data.Vec.Relation.Equality.Setoid {a ℓ} (S : Setoid a ℓ) where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Vec
open import Data.Vec.Relation.Pointwise.Inductive as PW
  using (Pointwise)
open import Function
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definition of equality

infix 4 _≋_

_≋_ : ∀ {m n} → REL (Vec A m) (Vec A n) ℓ
_≋_ = Pointwise _≈_

open Pointwise public using ([]; _∷_)
open PW public using (length-equal)

------------------------------------------------------------------------
-- Relational properties

≋-refl : ∀ {n} → Reflexive (_≋_ {n})
≋-refl = PW.refl refl

≋-sym : ∀ {n m} → Sym _≋_ (_≋_ {m} {n})
≋-sym = PW.sym sym

≋-trans : ∀ {n m o} → Trans (_≋_ {m}) (_≋_ {n} {o}) (_≋_)
≋-trans = PW.trans trans

≋-isEquivalence : ∀ n → IsEquivalence (_≋_ {n})
≋-isEquivalence = PW.isEquivalence isEquivalence

≋-setoid : ℕ → Setoid a ℓ
≋-setoid = PW.setoid S

------------------------------------------------------------------------
-- map

open PW public using ( map⁺)

------------------------------------------------------------------------
-- ++

open PW public using (++⁺ ; ++⁻ ; ++ˡ⁻; ++ʳ⁻)

++-identityˡ : ∀ {n} (xs : Vec A n) → [] ++ xs ≋ xs
++-identityˡ _ = ≋-refl

++-identityʳ : ∀ {n} (xs : Vec A n) → xs ++ [] ≋ xs
++-identityʳ []       = []
++-identityʳ (x ∷ xs) = refl ∷ ++-identityʳ xs

map-++-commute : ∀ {b m n} {B : Set b}
                   (f : B → A) (xs : Vec B m) {ys : Vec B n} →
                   map f (xs ++ ys) ≋ map f xs ++ map f ys
map-++-commute f []       = ≋-refl
map-++-commute f (x ∷ xs) = refl ∷ map-++-commute f xs

------------------------------------------------------------------------
-- concat

open PW public using (concat⁺; concat⁻)

------------------------------------------------------------------------
-- replicate

replicate-shiftʳ : ∀ {m} n x (xs : Vec A m) →
                  replicate {n = n}     x ++ (x ∷ xs) ≋
                  replicate {n = 1 + n} x ++      xs
replicate-shiftʳ zero    x xs = ≋-refl
replicate-shiftʳ (suc n) x xs = refl ∷ (replicate-shiftʳ n x xs)
