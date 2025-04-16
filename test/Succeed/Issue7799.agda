{-# OPTIONS -vtc.instance:30 -vtc.mod.apply:30 -vtc.constr.wake:90 #-}
module Issue7799 where

data D : Set where

record R (F : Set → Set) : Set₁ where
  field
    f : (A : Set) → F A

open R ⦃ … ⦄

postulate
  F₁ F₂ : Set → Set

instance postulate

  r₁ : R F₁
  r₂ : R F₂

module M (_ : F₁ D) where

open M (f D)
