
module MapTm where

open import Prelude
open import Star
open import Modal
open import Examples
open import Lambda

open Term

eq⟶ : {ty : Set}(T : TyAlg ty){σ₁ σ₂ τ₁ τ₂ : ty} ->
         σ₁ == σ₂ -> τ₁ == τ₂ -> TyAlg._⟶_ T σ₁ τ₁ == TyAlg._⟶_ T σ₂ τ₂
eq⟶ T refl refl = refl

mapTm : {ty₁ ty₂ : Set}{T₁ : TyAlg ty₁}{T₂ : TyAlg ty₂}
        {Γ : List ty₁}{τ : ty₁}(F : T₁ =Ty=> T₂) ->
        Tm T₁ Γ τ -> Tm T₂ (map _ (TyArrow.apply F) Γ) (TyArrow.apply F τ)
mapTm {T₁ = T₁}{T₂}{Γ} F (var x) =
  var (mapAny (cong (TyArrow.apply F)) x)
mapTm {T₁ = T₁}{T₂}{Γ} F zz =
  subst (\τ -> Tm T₂ (map _ (TyArrow.apply F) Γ) τ)
        (TyArrow.respNat F) zz
mapTm {T₁ = T₁}{T₂}{Γ} F ss =
  subst Tm₂ (trans (TyArrow.resp⟶ F)
                   (TyArrow.respNat F -eq⟶ TyArrow.respNat F))
        ss
  where
    _-eq⟶_ = eq⟶ T₂
    Tm₂ = Tm T₂ (map _ (TyArrow.apply F) Γ)
mapTm {T₂ = T₂}{Γ} F (ƛ t)   =
  subst Tm₂ (TyArrow.resp⟶ F)
        (ƛ (mapTm F t))
  where Tm₂ = Tm T₂ (map _ (TyArrow.apply F) Γ)
mapTm {T₂ = T₂}{Γ} F (s $ t) =
  subst Tm₂ (sym (TyArrow.resp⟶ F)) (mapTm F s)
  $ mapTm F t
  where
    Tm₂ = Tm T₂ (map _ (TyArrow.apply F) Γ)
