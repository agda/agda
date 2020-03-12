{-# OPTIONS --cubical --safe --no-sized-types --no-guardedness
            --no-subtyping #-}

module Agda.Builtin.Cubical.Glue where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Primitive.Cubical renaming (primINeg to ~_; primIMax to _∨_; primIMin to _∧_;
                                             primHComp to hcomp; primTransp to transp; primComp to comp;
                                             itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to ouc)
import Agda.Builtin.Cubical.HCompU as HCompU

module Helpers = HCompU.Helpers

open Helpers


-- We make this a record so that isEquiv can be proved using
-- copatterns. This is good because copatterns don't get unfolded
-- unless a projection is applied so it should be more efficient.
record isEquiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ') where
  no-eta-equality
  field
    equiv-proof : (y : B) → isContr (fiber f y)

open isEquiv public

infix 4 _≃_


_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) \ f → (isEquiv f)

equivFun : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → A → B
equivFun e = fst e

-- Improved version of equivProof compared to Lemma 5 in CCHM. We put
-- the (φ = i0) face in contr' making it be definitionally c in this
-- case. This makes the computational behavior better, in particular
-- for transp in Glue.
equivProof : ∀ {la lt} (T : Set la) (A : Set lt) → (w : T ≃ A) → (a : A)
           → ∀ ψ → (Partial ψ (fiber (w .fst) a)) → fiber (w .fst) a
equivProof A B w a ψ fb = contr' {A = fiber (w .fst) a} (w .snd .equiv-proof a) ψ fb
  where
    contr' : ∀ {ℓ} {A : Set ℓ} → isContr A → (φ : I) → (u : Partial φ A) → A
    contr' {A = A} (c , p) φ u = hcomp (λ i → λ { (φ = i1) → p (u 1=1) i
                                                ; (φ = i0) → c }) c


{-# BUILTIN EQUIV      _≃_        #-}
{-# BUILTIN EQUIVFUN   equivFun   #-}
{-# BUILTIN EQUIVPROOF equivProof #-}

primitive
    primGlue    : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
      → (T : Partial φ (Set ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
      → Set ℓ'
    prim^glue   : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
      → (t : PartialP φ T) → (a : A) → primGlue A T e
    prim^unglue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
      → primGlue A T e → A

    -- Needed for transp in Glue.
    primFaceForall : (I → I) → I


module _ {ℓ : I → Level} (P : (i : I) → Set (ℓ i)) where
  private
    E : (i : I) → Set (ℓ i)
    E  = λ i → P i
    ~E : (i : I) → Set (ℓ (~ i))
    ~E = λ i → P (~ i)

    A = P i0
    B = P i1

    f : A → B
    f x = transp E i0 x

    g : B → A
    g y = transp ~E i0 y

    u : ∀ i → A → E i
    u i x = transp (λ j → E (i ∧ j)) (~ i) x

    v : ∀ i → B → E i
    v i y = transp (λ j → ~E ( ~ i ∧ j)) i y

    fiberPath : (y : B) → (xβ0 xβ1 : fiber f y) → xβ0 ≡ xβ1
    fiberPath y (x0 , β0) (x1 , β1) k = ω , λ j → δ (~ j) where
      module _ (j : I) where
        private
          sys : A → ∀ i → PartialP (~ j ∨ j) (λ _ → E (~ i))
          sys x i (j = i0) = v (~ i) y
          sys x i (j = i1) = u (~ i) x
        ω0 = comp ~E (sys x0) ((β0 (~ j)))
        ω1 = comp ~E (sys x1) ((β1 (~ j)))
        θ0 = fill ~E (sys x0) (inc (β0 (~ j)))
        θ1 = fill ~E (sys x1) (inc (β1 (~ j)))
      sys = λ {j (k = i0) → ω0 j ; j (k = i1) → ω1 j}
      ω = hcomp sys (g y)
      θ = hfill sys (inc (g y))
      δ = λ (j : I) → comp E
            (λ i → λ { (j = i0) → v i y ; (k = i0) → θ0 j (~ i)
                     ; (j = i1) → u i ω ; (k = i1) → θ1 j (~ i) })
             (θ j)

    γ : (y : B) → y ≡ f (g y)
    γ y j = comp E (λ i → λ { (j = i0) → v i y
                            ; (j = i1) → u i (g y) }) (g y)

  pathToisEquiv : isEquiv f
  pathToisEquiv .equiv-proof y .fst .fst = g y
  pathToisEquiv .equiv-proof y .fst .snd = sym (γ y)
  pathToisEquiv .equiv-proof y .snd = fiberPath y _

  pathToEquiv : A ≃ B
  pathToEquiv .fst = f
  pathToEquiv .snd = pathToisEquiv
