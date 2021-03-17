{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  I : Set
  A : I → Set
  HEq : (i0 i1 : I) → A i0 → A i1 → Set
  HEq-on-refl : (i : I) (a0 a1 : A i) → HEq i i a0 a1 ≡ I
{-# REWRITE HEq-on-refl #-}

record Con : Set where
  field
    f : I → I
open Con public

postulate
  Ty : Con → Set

module M (Γ : Con) (_ : Ty Γ) where

  test : let aux1 : A (f Γ _)
             aux1 = _
             aux2 : A (f Γ _)
             aux2 = _
         in HEq _ _ aux1 aux2
  test = _
