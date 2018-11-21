{-# OPTIONS --cubical #-}
module _ where
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Sub
open import Agda.Primitive renaming (_⊔_ to ℓ-max)
open import Agda.Builtin.Sigma

private
  internalFiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ-max ℓ ℓ')
  internalFiber {A = A} f y = Σ A \ x → y ≡ f x

infix 4 _≃_

postulate
  _≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ-max ℓ ℓ')
  equivFun : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → A → B
  equivProof : ∀ {la lt} (T : Set la) (A : Set lt) → (w : T ≃ A) → (a : A)
               → ∀ ψ → (Partial ψ (internalFiber (equivFun w) a)) → internalFiber (equivFun w) a

{-# BUILTIN EQUIV _≃_ #-}
{-# BUILTIN EQUIVFUN  equivFun #-}
{-# BUILTIN EQUIVPROOF equivProof #-}

-- This is a module so we can easily rename the primitives.
module GluePrims where
  primitive
    primGlue    : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
      → (T : Partial φ (Set ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
      → Set ℓ'
    prim^glue   : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
      → PartialP φ T → A → primGlue A T e
    prim^unglue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
      → primGlue A T e → A

    -- Needed for transp in Glue.
    primFaceForall : (I → I) → I

open GluePrims public
  renaming ( prim^glue to glue
           ; prim^unglue to unglue)

-- We uncurry Glue to make it a bit more pleasant to use
Glue : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
       → (Te : Partial φ (Σ (Set ℓ') \ T →  T ≃ A))
       → Set ℓ'
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

module _ {ℓ ℓ'} (A : Set ℓ) {φ : I} (Te : Partial φ (Σ (Set ℓ') \ T →  T ≃ A))
         (ψ : I) (u : I → Partial ψ (Glue A Te)) (u0 : Sub (Glue A Te) ψ (u i0) ) where
  result : Glue A Te
  result = glue {φ = φ} (\ { (φ = i1) → primHComp {A = Te itIsOne .fst} u (primSubOut u0) })
                        (primHComp {A = A} (\ i → \ { (ψ = i1) → unglue {φ = φ} (u i itIsOne)
                                                    ; (φ = i1) → equivFun (Te itIsOne .snd)
                                                                          (primHComp (\ j → \ { (ψ = i1) → u (primIMin i j) itIsOne
                                                                                              ; (i = i0) → primSubOut u0 })
                                                                                     (primSubOut u0)) })
                                           (unglue {φ = φ} (primSubOut u0)))

  test : primHComp {A = Glue A Te} {ψ} u (primSubOut u0) ≡ result
  test i = primHComp {A = Glue A Te} {ψ} u (primSubOut u0)
