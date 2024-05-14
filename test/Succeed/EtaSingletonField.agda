-- 2024-03-12 PR #7180: Missing eta in conversion checker.

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
  -- Check _1 : Hom ⊤ ⊤
  tm ← checkType unknown (quoteTerm (Hom ⊤ ⊤))
  -- Check (id (Hom.hom _1 tt)) : ⊤
  tm' ← checkType
    (def (quote id) (argN (def (quote Hom.hom) (argN tm ∷ argN (quoteTerm tt) ∷ [])) ∷ []))
    (quoteTerm ⊤)
  -- Unify (Hom.hom fun tt) ?= (id (Hom.hom _1 tt))
  unify (quoteTerm (Hom.hom fun tt)) tm'


-- Error was (until < 2.6.5)
--
-- tt != Hom.hom fun tt of type ⊤
-- when checking that the expression
-- unquote
-- λ goal →
--   checkType unknown (quoteTerm (Hom ⊤ ⊤)) >>=
--   (λ tm →
--      checkType
--      (def (quote id)
--       (argN (def (quote Hom.hom) (argN tm ∷ argN (quoteTerm tt) ∷ [])) ∷
--        []))
--      (quoteTerm ⊤)
--      >>= (λ tm' → unify (quoteTerm (Hom.hom fun tt)) tm'))
-- has type ⊤

-- Should succeed with an unsolved meta.
-- _it_47 : wit  [ at ... ]
