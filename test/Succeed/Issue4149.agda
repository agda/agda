{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive

postulate
  A : Set
  F : ∀ {ℓ} (XF : Set ℓ) → Set ℓ

record R (Q : ∀ {ℓ} (XQ : Set ℓ) → Set ℓ) ℓ : Set (lsuc ℓ) where
  field
    f : {A : Set ℓ} (fa : F A) → Q A

open R

module M (X : Set₁) where
  postulate
    G : ∀ {ℓ} (XG : Set ℓ) → Set ℓ

module N (Y : Set) where
  open M Set

  variable
    z : F A

  postulate
    P     : (p : G A) → Set
    fails : P (f _ z)
