{-# OPTIONS --cubical --safe --no-sized-types --no-guardedness
            --no-subtyping #-}

module Agda.Builtin.Cubical.HCompU where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Primitive.Cubical renaming (primINeg to ~_; primIMax to _∨_; primIMin to _∧_;
                                             primHComp to hcomp; primTransp to transp; primComp to comp;
                                             itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to outS; inc to inS)

module Helpers where
    -- Homogeneous filling
    hfill : ∀ {ℓ} {A : Set ℓ} {φ : I}
              (u : ∀ i → Partial φ A)
              (u0 : A [ φ ↦ u i0 ]) (i : I) → A
    hfill {φ = φ} u u0 i =
      hcomp (λ j → \ { (φ = i1) → u (i ∧ j) 1=1
                     ; (i = i0) → outS u0 })
            (outS u0)

    -- Heterogeneous filling defined using comp
    fill : ∀ {ℓ : I → Level} (A : ∀ i → Set (ℓ i)) {φ : I}
             (u : ∀ i → Partial φ (A i))
             (u0 : A i0 [ φ ↦ u i0 ]) →
             ∀ i →  A i
    fill A {φ = φ} u u0 i =
      comp (λ j → A (i ∧ j))
           (λ j → \ { (φ = i1) → u (i ∧ j) 1=1
                    ; (i = i0) → outS u0 })
           (outS {φ = φ} u0)

    module _ {ℓ} {A : Set ℓ} where
      refl : {x : A} → x ≡ x
      refl {x = x} = λ _ → x

      sym : {x y : A} → x ≡ y → y ≡ x
      sym p = λ i → p (~ i)

      cong : ∀ {ℓ'} {B : A → Set ℓ'} {x y : A}
             (f : (a : A) → B a) (p : x ≡ y)
           → PathP (λ i → B (p i)) (f x) (f y)
      cong f p = λ i → f (p i)

    isContr : ∀ {ℓ} → Set ℓ → Set ℓ
    isContr A = Σ A \ x → (∀ y → x ≡ y)

    fiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ ⊔ ℓ')
    fiber {A = A} f y = Σ A \ x → f x ≡ y

open Helpers


primitive
  prim^glueU : {la : Level} {φ : I} {T : I → Partial φ (Set la)}
                 {A : Set la [ φ ↦ T i0 ]} →
                 PartialP φ (T i1) → outS A → hcomp T (outS A)
  prim^unglueU : {la : Level} {φ : I} {T : I → Partial φ (Set la)}
                   {A : Set la [ φ ↦ T i0 ]} →
                   hcomp T (outS A) → outS A

transpProof : ∀ {l} → (e : I → Set l) → (φ : I) → (a : Partial φ (e i0)) → (b : e i1 [ φ ↦ (\ o → transp e i0 (a o)) ] ) → fiber (transp e i0) (outS b)
transpProof e φ a b = f , \ j → comp e (\ i → \ { (φ = i1) → transp (\ j → e (j ∧ i)) (~ i) (a 1=1)
                                                 ; (j = i0) → transp (\ j → e (j ∧ i)) (~ i) f
                                                 ; (j = i1) → g (~ i) })
                                        f
    where
      g = fill (\ i → e (~ i)) (\ i → \ { (φ = i1) → transp (\ j → e (j ∧ ~ i)) i (a 1=1); (φ = i0) → transp (\ j → e (~ j ∨ ~ i)) (~ i) (outS b) }) (inS (outS b))
      f = comp (\ i → e (~ i)) (\ i → \ { (φ = i1) → transp (\ j → e (j ∧ ~ i)) i (a 1=1); (φ = i0) → transp (\ j → e (~ j ∨ ~ i)) (~ i) (outS b) }) (outS b)

{-# BUILTIN TRANSPPROOF transpProof #-}
