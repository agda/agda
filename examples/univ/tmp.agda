
module tmp where

open import univ
open import cwf
open import Base
open import Nat
open import help
open import proofs

{- TODO: Prove

  w = λ ((w // wk) ∙ vz)    (η)

  λ v // σ = λ (v // (σ ∘ wk ,, vz))
  w ∙ u // σ = (w // σ) ∙ (u // σ)

-}

{-
lem-tmp : {Γ : Con}{A : Type Γ}(B : Type (Γ , A)) ->
	  Π A B =Ty Π A (B / (wk ∘ wk ,, castElem ? vz) / [ vz ])
lem-tmp B = ?

lem-η : {Γ : Con}{A : Type Γ}{B : Type (Γ , A)}(w : Elem Γ (Π A B)) ->
	w =El castElem (lem-tmp B)
	      (λ {A = A}
		 (castElem (symTy (lem-Π/ B wk)) (w // wk {A = A}) ∙ vz)
	      )
lem-η (elem (el < w , pw >)) = ?
-}
