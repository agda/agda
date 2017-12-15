------------------------------------------------------------------------
-- The Agda standard library
--
-- Semi-heterogeneous vector equality
------------------------------------------------------------------------

module Data.Vec.Relation.Equality where

open import Data.Vec
open import Data.Nat.Base using (suc)
open import Function
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
module Equality {s₁ s₂} (S : Setoid s₁ s₂) where

  private
    open module SS = Setoid S
      using () renaming (_≈_ to _≊_; Carrier to A)

  infix 4 _≈_

  data _≈_ : ∀ {n¹} → Vec A n¹ →
             ∀ {n²} → Vec A n² → Set (s₁ ⊔ s₂) where
    []-cong  : [] ≈ []
    _∷-cong_ : ∀ {x¹ n¹} {xs¹ : Vec A n¹}
                 {x² n²} {xs² : Vec A n²}
                 (x¹≈x² : x¹ ≊ x²) (xs¹≈xs² : xs¹ ≈ xs²) →
                 x¹ ∷ xs¹ ≈ x² ∷ xs²

  length-equal : ∀ {n¹} {xs¹ : Vec A n¹}
                   {n²} {xs² : Vec A n²} →
                 xs¹ ≈ xs² → n¹ ≡ n²
  length-equal []-cong        = P.refl
  length-equal (_ ∷-cong eq₂) = P.cong suc $ length-equal eq₂

  refl : ∀ {n} (xs : Vec A n) → xs ≈ xs
  refl []       = []-cong
  refl (x ∷ xs) = SS.refl ∷-cong refl xs

  sym : ∀ {n m} {xs : Vec A n} {ys : Vec A m} →
        xs ≈ ys → ys ≈ xs
  sym []-cong                = []-cong
  sym (x¹≡x² ∷-cong xs¹≈xs²) = SS.sym x¹≡x² ∷-cong sym xs¹≈xs²

  trans : ∀ {n m l} {xs : Vec A n} {ys : Vec A m} {zs : Vec A l} →
          xs ≈ ys → ys ≈ zs → xs ≈ zs
  trans []-cong            []-cong            = []-cong
  trans (x≈y ∷-cong xs≈ys) (y≈z ∷-cong ys≈zs) =
    SS.trans x≈y y≈z ∷-cong trans xs≈ys ys≈zs

  xs++[]≈xs : ∀ {n} (xs : Vec A n) → xs ++ [] ≈ xs
  xs++[]≈xs []        = []-cong
  xs++[]≈xs (x ∷ xs) = SS.refl ∷-cong (xs++[]≈xs xs)

  _++-cong_ : ∀ {n₁¹ n₂¹} {xs₁¹ : Vec A n₁¹} {xs₂¹ : Vec A n₂¹}
                {n₁² n₂²} {xs₁² : Vec A n₁²} {xs₂² : Vec A n₂²} →
              xs₁¹ ≈ xs₁² → xs₂¹ ≈ xs₂² →
              xs₁¹ ++ xs₂¹ ≈ xs₁² ++ xs₂²
  []-cong          ++-cong eq₃ = eq₃
  (eq₁ ∷-cong eq₂) ++-cong eq₃ = eq₁ ∷-cong (eq₂ ++-cong eq₃)

module DecidableEquality {d₁ d₂} (D : DecSetoid d₁ d₂) where

  private module DS = DecSetoid D
  open DS using () renaming (_≟_ to _≟′_ ; Carrier to A)
  open Equality DS.setoid
  open import Relation.Nullary

  infix 4 _≟_

  _≟_ : ∀ {n m} (xs : Vec A n) (ys : Vec A m) → Dec (xs ≈ ys)
  _≟_ []       []       = yes []-cong
  _≟_ []       (y ∷ ys) = no (λ())
  _≟_ (x ∷ xs) []       = no (λ())
  _≟_ (x ∷ xs) (y ∷ ys) with xs ≟ ys | x ≟′ y
  ... | yes xs≈ys | yes x≊y = yes (x≊y ∷-cong xs≈ys)
  ... | no ¬xs≈ys | _       = no helper
    where
    helper : ¬ (x ∷ xs ≈ y ∷ ys)
    helper (_ ∷-cong xs≈ys) = ¬xs≈ys xs≈ys
  ... | _         | no ¬x≊y = no helper
    where
    helper : ¬ (x ∷ xs ≈ y ∷ ys)
    helper (x≊y ∷-cong _) = ¬x≊y x≊y

module PropositionalEquality {a} {A : Set a} where

  open Equality (P.setoid A) public

  to-≡ : ∀ {n} {xs ys : Vec A n} → xs ≈ ys → xs ≡ ys
  to-≡ []-cong                 = P.refl
  to-≡ (P.refl ∷-cong xs¹≈xs²) = P.cong (_∷_ _) $ to-≡ xs¹≈xs²

  from-≡ : ∀ {n} {xs ys : Vec A n} → xs ≡ ys → xs ≈ ys
  from-≡ P.refl = refl _

  to-≅ : ∀ {m n} {xs : Vec A m} {ys : Vec A n} →
            xs ≈ ys → xs ≅ ys
  to-≅ p with length-equal p
  to-≅ p | P.refl = H.≡-to-≅ (to-≡ p)

  xs++[]≅xs : ∀ {n} → (xs : Vec A n) → (xs ++ []) ≅ xs
  xs++[]≅xs xs = to-≅ (xs++[]≈xs xs)
