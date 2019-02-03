-- Verify that issue 3415 has been fixed by checking that the
-- computation rule for univalence holds up to a trivial transport (it
-- used to only hold up to a more complicated argument).
{-# OPTIONS --cubical #-}
module Issue3415 where

open import Agda.Primitive.Cubical public
open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Cubical.Glue public
open import Agda.Builtin.Sigma public

idIsEquiv : ∀ {ℓ} (A : Set ℓ) → isEquiv (λ (x : A) → x)
equiv-proof (idIsEquiv A) y =
  ((y , λ _ → y) , λ z i → z .snd (primINeg i)
  , λ j → z .snd (primIMax (primINeg i) j))

idEquiv : ∀ {ℓ} (A : Set ℓ) → A ≃ A
idEquiv A = ((λ x → x) , idIsEquiv A)

ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
ua {A = A} {B = B} e i =
  primGlue B (λ { (i = i0) → A ; (i = i1) → B })
             (λ { (i = i0) → e ; (i = i1) → (idEquiv B) })

transport : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
transport p a = primTransp (λ i → p i) i0 a

transportRefl : ∀ {ℓ}  {A : Set ℓ} → (x : A) → transport (λ _ → A) x ≡ x
transportRefl {A = A} x i = primTransp (λ _ → A) i x

uaβ : ∀ {ℓ} {A B : Set ℓ} (e : A ≃ B) (x : A) → transport (ua e) x ≡ e .fst x
uaβ e x = transportRefl (e .fst x)
