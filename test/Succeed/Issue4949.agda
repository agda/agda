{-# OPTIONS --cubical --safe #-}
module Issue4949 where

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical renaming (primIMax to _∨_)
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma

open import Agda.Builtin.Cubical.Glue renaming (prim^glue to glue)

idIsEquiv : ∀ {ℓ} (A : Set ℓ) → isEquiv (\ (x : A) → x)
equiv-proof (idIsEquiv A) y =
  ((y , \ _ → y) , λ z i → z .snd (primINeg i) , λ j → z .snd (primINeg i ∨ j))

idEquiv : ∀ {ℓ} (A : Set ℓ) → Σ _ (isEquiv {A = A} {B = A})
idEquiv A .fst = \ x → x
idEquiv A .snd = idIsEquiv A

Glue : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
       → (Te : Partial φ (Σ (Set ℓ') \ T → Σ _ (isEquiv {A = T} {B = A})))
       → Set ℓ'
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                   ; (i = i1) → (B , idEquiv B) })


⊤₀ = ⊤
⊤₁ = Σ ⊤ \ _ → ⊤

prf : isEquiv {A = ⊤₀} {B = ⊤₁} _
equiv-proof prf y = (_ , \ i → _) , (\ y → \ i → _ , (\ j → _))

u : ⊤₀ ≡ ⊤₁
u = ua ((λ _ → _) , prf)

uniq : ∀ i j → u (i ∨ j)
uniq i j = glue (λ { (i = i0) (j = i0) → tt ; (i = i1) → tt , tt ; (j = i1) → tt , tt }) _

-- comparing the partial element argument of `glue` should happen at the right type.
-- if it does not we get problems with eta.
test : ∀ j → uniq i0 j ≡ glue (λ { (i0 = i0) (j = i0) → tt ; (j = i1) → tt , tt }) (tt , tt)
test j = \ k → uniq i0 j
