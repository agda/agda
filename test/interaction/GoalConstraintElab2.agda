{-# OPTIONS --cubical #-}

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Glue
open import Agda.Builtin.Cubical.Id
open import Agda.Builtin.Sigma
open import Agda.Primitive.Cubical
  renaming
    ( primIMax to _∨_
    ; primIMin to _∧_
    ; primINeg to ~_
    ; primComp to comp
    ; primHComp to primHComp
    ; primTransp to transp
    ; itIsOne to 1=1
    )

Square : ∀ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
       → (p : a00 ≡ a01)
       → (q : a00 ≡ a10)
       → (s : a01 ≡ a11)
       → (r : a10 ≡ a11)
       → Type ℓ
Square p q s r = PathP (λ i → p i ≡ r i) q s

no-negative-boundary
  : ∀ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
  → (p : a00 ≡ a01)
  → (q : a00 ≡ a10)
  → (s : a01 ≡ a11)
  → (r : a10 ≡ a11)
  → PathP (λ i → p i ≡ r i) q s → Square p q s r

-- The interaction point here *technically* has face constraints keyed
-- by the negative-first variable (i.e. the next variable in the
-- context/an argument we have not yet introduced a lambda for) in the
-- context. We shouldn't show these:
no-negative-boundary p q s r sq = λ i → {! λ (j : I) → sq i j  !}
