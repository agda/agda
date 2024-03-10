{-# OPTIONS --allow-unsolved-metas #-}
module EtaSingletonField where

open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Unit
open import Agda.Builtin.List

postulate wit : Set

record Hom (X Y : Set) : Set where
  field
    hom : X → Y
    it : wit

argN : ∀ {ℓ} {A : Set ℓ} → A → Arg A
argN = arg (arg-info visible (modality relevant quantity-ω))

postulate fun : Hom ⊤ ⊤

id : ∀ {ℓ} {A : Set ℓ} → A → A
id x = x

_ : ⊤
_ = unquote λ goal → do
  tm ← checkType unknown (quoteTerm (Hom ⊤ ⊤))
  tm' ← checkType
    (def (quote id) (argN (def (quote Hom.hom) (argN tm ∷ argN (quoteTerm tt) ∷ [])) ∷ [])) (quoteTerm ⊤)
  unify (quoteTerm (Hom.hom fun tt)) tm'
