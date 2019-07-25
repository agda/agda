{-# OPTIONS --cubical --no-sized-types --no-guardedness #-}
module Agda.Builtin.Cubical.HCompU where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Primitive.Cubical renaming (primINeg to ~_; primIMax to _∨_; primIMin to _∧_;
                                             primHComp to hcomp; primTransp to transp; primComp to comp;
                                             itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to ouc)

module Helpers where
    -- Homogeneous filling
    hfill : ∀ {ℓ} {A : Set ℓ} {φ : I}
              (u : ∀ i → Partial φ A)
              (u0 : A [ φ ↦ u i0 ]) (i : I) → A
    hfill {φ = φ} u u0 i =
      hcomp (λ j → \ { (φ = i1) → u (i ∧ j) 1=1
                     ; (i = i0) → ouc u0 })
            (ouc u0)

    -- Heterogeneous filling defined using comp
    fill : ∀ {ℓ : I → Level} (A : ∀ i → Set (ℓ i)) {φ : I}
             (u : ∀ i → Partial φ (A i))
             (u0 : A i0 [ φ ↦ u i0 ]) →
             ∀ i →  A i
    fill A {φ = φ} u u0 i =
      comp (λ j → A (i ∧ j))
           (λ j → \ { (φ = i1) → u (i ∧ j) 1=1
                    ; (i = i0) → ouc u0 })
           (ouc {φ = φ} u0)

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

    ΣPathP : ∀ {la lb} {A : Set la}{B : A → Set lb} {x y : Σ A B} → (p : x .fst ≡ y .fst) → PathP (\ i → B (p i)) (x .snd) (y .snd) → x ≡ y
    ΣPathP p q i .fst = p i
    ΣPathP p q i .snd = q i

open Helpers


primitive
  primHCompU : _
  prim^glueU : _
  prim^unglueU : _


transpProof : ∀ {l} → (e : I → Set l) → (b : e i1) → (φ : I) → Partial φ (fiber (transp e i0) b) → fiber (transp e i0) b
transpProof {l} e b φ u = contr' (ce b) φ u
  where
    contr' : ∀ {ℓ} {A : Set ℓ} → isContr A → (φ : I) → (u : Partial φ A) → A
    contr' {A = A} (c , p) φ u = hcomp (λ i → λ { (φ = i1) → p (u 1=1) i
                                                ; (φ = i0) → c }) c
    isEquiv : {A B : Set l} (f : A → B) → Set _
    isEquiv f = (b : _) → isContr (fiber f b)

    cid : (b : e i0) → isContr (fiber (\ x → x) b)
    cid b .fst = (b , refl)
    cid b .snd = (\ y → \ i → sym (snd y) i , \ j → snd y (~ i ∨ j) )

    -- TODO: is it possible to get a smaller normal form for this or transpProof? daghstul lemma?
    ce : isEquiv (transp e i0)
    ce b = transp (\ i → isEquiv (\ x → transp (\ j → e (i ∧ j)) (~ i) x)) i0 cid b

{-# BUILTIN TRANSPPROOF transpProof #-}
