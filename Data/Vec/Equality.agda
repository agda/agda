------------------------------------------------------------------------
-- Semi-heterogeneous vector equality
------------------------------------------------------------------------

module Data.Vec.Equality where

open import Data.Vec
open import Data.Nat using (suc)
open import Data.Function
open import Relation.Binary
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_)

module Equality (S : Setoid) where

  open Setoid S renaming (_≈_ to _≊_ ; carrier to a ; refl to refl' ; sym to sym' ; trans to trans')

  infix 4 _≈_

  data _≈_ : ∀ {n¹} → Vec a n¹ →
             ∀ {n²} → Vec a n² → Set where
    []-cong  : [] ≈ []
    _∷-cong_ : ∀ {x¹ n¹} {xs¹ : Vec a n¹}
                 {x² n²} {xs² : Vec a n²}
                 (x¹≈x² : x¹ ≊ x²) (xs¹≈xs² : xs¹ ≈ xs²) →
                 x¹ ∷ xs¹ ≈ x² ∷ xs²

  length-equal : ∀ {n¹} {xs¹ : Vec a n¹}
                   {n²} {xs² : Vec a n²} →
                   xs¹ ≈ xs² → n¹ ≡ n²
  length-equal []-cong        = PropEq.refl
  length-equal (_ ∷-cong eq₂) = PropEq.cong suc $ length-equal eq₂

  refl : ∀ {n} (xs : Vec a n) → xs ≈ xs
  refl []       = []-cong
  refl (x ∷ xs) = refl' ∷-cong refl xs

  sym : ∀ {n m}{xs : Vec a n}{ys : Vec a m} → xs ≈ ys → ys ≈ xs
  sym []-cong = []-cong
  sym (x¹≡x² ∷-cong xs¹≈xs²) = (sym' x¹≡x²) ∷-cong (sym xs¹≈xs²)

  trans : ∀ {n m l}{xs : Vec a n}{ys : Vec a m}{zs : Vec a l} → xs ≈ ys → ys ≈ zs → xs ≈ zs
  trans []-cong []-cong = []-cong
  trans (x≈y ∷-cong xs≈ys) (y≈z ∷-cong ys≈zs) = (trans' x≈y y≈z) ∷-cong (trans xs≈ys ys≈zs)

  _++-cong_ : ∀ {n₁¹ n₂¹} {xs₁¹ : Vec a n₁¹} {xs₂¹ : Vec a n₂¹}
                {n₁² n₂²} {xs₁² : Vec a n₁²} {xs₂² : Vec a n₂²} →
                xs₁¹ ≈ xs₁² → xs₂¹ ≈ xs₂² →
                xs₁¹ ++ xs₂¹ ≈ xs₁² ++ xs₂²
  []-cong          ++-cong eq₃ = eq₃
  (eq₁ ∷-cong eq₂) ++-cong eq₃ = eq₁ ∷-cong (eq₂ ++-cong eq₃)

module DecidableEquality (D : DecSetoid) where

  open DecSetoid D hiding (_≈_) renaming (_≟_ to _≟'_ ; carrier to a)
  open Equality setoid
  open import Relation.Nullary

  _≟_ : ∀{n m}(xs : Vec a n)(ys : Vec a m) → Dec (xs ≈ ys)
  _≟_ [] [] = yes []-cong
  _≟_ [] (y ∷ ys) = no (λ())
  _≟_ (x ∷ xs) [] = no (λ())
  _≟_ (x ∷ xs) (y ∷ ys) with xs ≟ ys | x ≟' y
  ... | yes xs≈ys | yes x≊y = yes (x≊y ∷-cong xs≈ys)
  ... | no ¬xs≈ys | _ = no helper
    where
      helper : ¬ (x ∷ xs) ≈ (y ∷ ys)
      helper (_ ∷-cong xs≈ys) = ¬xs≈ys xs≈ys
  ... | _ | no ¬x≊y = no helper
    where
      helper : ¬ (x ∷ xs) ≈ (y ∷ ys)
      helper (x≊y ∷-cong _) = ¬x≊y x≊y

module HeterogeneousEquality (a : Set) where

  import Relation.Binary.HeterogeneousEquality as HetEq
  open HetEq using (_≅_)
  open Equality (PropEq.setoid a)

  to-≅ : ∀ {n m}{xs : Vec a n}{ys : Vec a m} 
        → xs ≈ ys → xs ≅ ys
  to-≅ []-cong = HetEq.refl
  to-≅ (PropEq.refl ∷-cong xs¹≈xs²) with length-equal xs¹≈xs²
  ... | PropEq.refl = HetEq.cong (_∷_ _) $ to-≅ xs¹≈xs²