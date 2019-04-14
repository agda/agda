{-# OPTIONS --cubical --safe #-}

module Issue3577 where

open import Agda.Primitive.Cubical renaming (primTransp to transp; primHComp to hcomp)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Sigma
open import Agda.Builtin.Cubical.Sub renaming (primSubOut to ouc; Sub to _[_↦_])
refl : ∀ {l} {A : Set l} {x : A} → x ≡ x
refl {x = x} = \ _ → x

ptType : Set₁
ptType = Σ Set (λ A → A)

data Susp' (A : ptType) : Set where
  susp*  : Susp' A
  merid' : (a : A .fst) → susp* ≡ susp*
  base'  : merid' (A .snd) ≡ refl

-- computation of transp on HIT's hcomp
testTr : {A' : ptType} (ψ : I) (A : I → ptType [ ψ ↦ (\ _ → A') ])
         {φ : I}
         (u : ∀ i → Partial φ (Susp' (ouc (A i0))))
         (u0 : Susp' (ouc (A i0)) [ φ ↦ u i0 ])
         → transp (\ i -> Susp' (ouc (A i))) ψ (hcomp u (ouc u0))
         ≡ hcomp (λ j .o → transp (λ i → Susp' (ouc (A i))) ψ (u j o)) (transp (λ i → Susp' (ouc (A i))) ψ (ouc u0))
testTr ψ A u u0 = refl
