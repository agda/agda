{-# OPTIONS --cubical #-}
module _ where
open import Agda.Primitive.Cubical renaming (primINeg to ~_; primIMax to _∨_; primIMin to _∧_)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Sub
open import Agda.Builtin.Cubical.Sub using () renaming (Sub to _[_↦_]; primSubOut to ouc)
open import Agda.Primitive renaming (_⊔_ to ℓ-max)
open import Agda.Builtin.Sigma

transpFill : ∀ {ℓ} {A' : Set ℓ} (φ : I)
               (A : (i : I) → Set ℓ [ φ ↦ (\ _ → A') ]) →
               (u0 : ouc (A i0)) →
               PathP (λ i → ouc (A i)) u0 (primTransp (λ i → ouc (A i)) φ u0)
transpFill φ A u0 i = primTransp (\ j → ouc (A (i ∧ j))) (~ i ∨ φ) u0

forward : (la : I → Level) (A : ∀ i → Set (la i)) (r : I) → A r → A i1
forward la A r x = primTransp (\ i → A (i ∨ r)) r x

-- gcomp^i A [ phi -> u ] u0 = hcomp^i A(1/i) [ phi -> forward A i u, ~ phi -> forward A 0 u ] (forward A 0 u0)

gcomp : ∀ {l} (A : I → Set l) (φ : I) (u : ∀ i → Partial φ (A i)) (u0 : A i0 [ φ ↦ u i0 ]) -> A i1
gcomp A φ u u0 = primHComp {A = A i1} (\ i → \ { (φ = i1) →  forward _ A i (u i itIsOne); (φ = i0) →  forward _ A i0 (ouc u0) })
                                         (forward _ A i0 (ouc u0))

-- private
--   internalFiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ-max ℓ ℓ')
--   internalFiber {A = A} f y = Σ A \ x → y ≡ f x

-- infix 4 _≃_

-- postulate
--   _≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ-max ℓ ℓ')
--   equivFun : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → A → B
--   equivProof : ∀ {la lt} (T : Set la) (A : Set lt) → (w : T ≃ A) → (a : A)
--                → ∀ ψ → (Partial ψ (internalFiber (equivFun w) a)) → internalFiber (equivFun w) a

-- {-# BUILTIN EQUIV _≃_ #-}
-- {-# BUILTIN EQUIVFUN  equivFun #-}
-- {-# BUILTIN EQUIVPROOF equivProof #-}

-- -- This is a module so we can easily rename the primitives.
-- module GluePrims where
--   primitive
--     primGlue    : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
--       → (T : Partial φ (Set ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
--       → Set ℓ'
--     prim^glue   : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
--       → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
--       → PartialP φ T → A → primGlue A T e
--     prim^unglue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
--       → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
--       → primGlue A T e → A

--     -- Needed for transp in Glue.
--     primFaceForall : (I → I) → I

open import Agda.Builtin.Cubical.Glue public
  renaming ( prim^glue to glue
           ; prim^unglue to unglue)

-- We uncurry Glue to make it a bit more pleasant to use
Glue : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
       → (Te : Partial φ (Σ (Set ℓ') \ T →  T ≃ A))
       → Set ℓ'
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)


-- Here we test that hcomp and transp for Glue compute as expected.
-- The current implementation in Agda.TypeChecking.Primitive does not
-- guarantee that the terms are well-typed, so making sure that those
-- primitives compute to some well-typed terms helps catching typing
-- bugs.

module TestHComp {ℓ ℓ'} (A : Set ℓ) {φ : I} (Te : Partial φ (Σ (Set ℓ') \ T →  T ≃ A))
         (ψ : I) (u : I → Partial ψ (Glue A Te)) (u0 : Sub (Glue A Te) ψ (u i0) ) where
  result : Glue A Te
  result = glue {φ = φ} (\ { (φ = i1) → primHComp {A = Te itIsOne .fst} u (primSubOut u0) })
                        (primHComp {A = A} (\ i → \ { (ψ = i1) → unglue {φ = φ} (u i itIsOne)
                                                    ; (φ = i1) → equivFun (Te itIsOne .snd)
                                                                          (primHComp (\ j → \ { (ψ = i1) → u (i ∧ j) itIsOne
                                                                                              ; (i = i0) → primSubOut u0 })
                                                                                     (primSubOut u0)) })
                                           (unglue {φ = φ} (primSubOut u0)))

  test : primHComp {A = Glue A Te} {ψ} u (primSubOut u0) ≡ result
  test i = primHComp {A = Glue A Te} {ψ} u (primSubOut u0)


module TestTransp {ℓ ℓ'} (A : Set ℓ) {φ : I} (Te : Partial φ (Σ (Set ℓ') \ T →  T ≃ A))
         (u0 : (Glue A Te)) where
  ψ = i0

  a0 = unglue {φ = φ} u0
  a1 = gcomp (\ _ → A)
         φ
         (\ { i (φ = i1) → equivFun (Te itIsOne .snd) (transpFill {A' = Te itIsOne .fst} ψ (\ i → inc (Te itIsOne .fst)) u0 i) })
         (inc a0)

  pair : PartialP φ λ o → Helpers.fiber (Te o .snd .fst) a1
  pair o = equivProof (Te o .fst) A (Te o .snd) a1 φ \ { (φ = i1) → _ , Helpers.refl }

  result : Glue A Te
  result = glue {φ = φ} (λ o → pair o .fst) (primHComp (\ { j (φ = i1) → pair itIsOne .snd j}) a1)

  test : primTransp (\ _ → Glue A Te) ψ u0 ≡ result
  test = Helpers.refl
