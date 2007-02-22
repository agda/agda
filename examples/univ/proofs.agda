
module proofs where

open import univ
open import cwf
open import Base
open import Nat
open import help

lem-id∘ : {Γ Δ : Con}(σ : Γ ─→ Δ) -> id ∘ σ == σ
lem-id∘ (el < σ , pσ >) = eq \x -> ref

lem-∘id : {Γ Δ : Con}(σ : Γ ─→ Δ) -> σ ∘ id == σ
lem-∘id (el < σ , pσ >) = eq \x -> ref

lem-∘assoc : {Γ Δ Θ Ξ : Con}(σ : Θ ─→ Ξ)(δ : Δ ─→ Θ)(θ : Γ ─→ Δ) ->
             (σ ∘ δ) ∘ θ == σ ∘ (δ ∘ θ)
lem-∘assoc (el < σ , pσ >) (el < δ , pδ >) (el < θ , pθ >) = eq \x -> ref

lem-/∘ : {Γ Δ Θ : Con}(A : Type Γ)(σ : Δ ─→ Γ)(δ : Θ ─→ Δ) ->
         A / σ ∘ δ =Ty A / σ / δ
lem-/∘ A (el < _ , _ >) (el < _ , _ >) = eqTy \x -> refS

lem-//id : {Γ : Con}{A : Type Γ}{u : Elem Γ A} -> u // id == castElem lem-/id u
lem-//id {Γ}{A}{el < u , pu >} = eq prf
  where
    prf : (x : El Γ) -> _
    prf x =
      chain> u x
         === _ << u (refS << x) by pu (sym (ref<< x))
         === _ << u (refS << x) by pfi _ _ _
      where open module C11 = Chain _==_ (ref {_}) (trans {_})

lem-//∘ : {Γ Δ Θ : Con}{A : Type Γ}(u : Elem Γ A)(σ : Δ ─→ Γ)(δ : Θ ─→ Δ) ->
          u // σ ∘ δ == castElem (lem-/∘ A σ δ) (u // σ // δ)
lem-//∘ {Γ}{Δ}{Θ} (el < u , pu >) σ'@(el < σ , _ >) δ'@(el < δ , _ >) = eq prf
  where
    prf : (x : El Θ) -> _
    prf x =
      chain> u (σ (δ x))
         === _ << u (σ (δ (refS << x))) by pu (p─→ σ' (p─→ δ' (sym (ref<< x))))
         === _ << u (σ (δ (refS << x))) by pfi _ _ _
      where open module C12 = Chain _==_ (ref {_}) (trans {_})

lem-wk∘σ,,u : {Γ Δ : Con}{A : Type Γ}(σ : Δ ─→ Γ)(u : Elem Δ (A / σ)) ->
              wk ∘ (σ ,, u) == σ
lem-wk∘σ,,u (el < σ , pσ >) (el < u , pu >) = eq \x -> ref

lem-/wk∘σ,,u : {Γ Δ : Con}(A : Type Γ)(σ : Δ ─→ Γ)(u : Elem Δ (A / σ)) ->
               A / wk / (σ ,, u) =Ty A / σ
lem-/wk∘σ,,u A (el < σ , pσ >) (el < u , pu >) = eqTy \x -> refS

lem-vz/σ,,u : {Γ Δ : Con}{A : Type Γ}(σ : Δ ─→ Γ)(u : Elem Δ (A / σ)) ->
              vz // (σ ,, u) == castElem (lem-/wk∘σ,,u A σ u) u
lem-vz/σ,,u (el < σ , pσ >) (el < u , pu >) = eq \x -> prf x
  where
    prf : (x : El _) -> u x == _ << u (refS << x)
    prf x =
      chain> u x
         === _ << u (refS << x) by pu (sym (ref<< x))
         === _ << u (refS << x) by pfi _ _ _
      where open module C15 = Chain _==_ (ref {_}) (trans {_})

lem-σ,,u∘ : {Γ Δ Θ : Con}{A : Type Γ}
            (σ : Δ ─→ Γ)(u : Elem Δ (A / σ))(δ : Θ ─→ Δ) ->
            (σ ,, u) ∘ δ == (σ ∘ δ ,, castElem (lem-/∘ A σ δ) (u // δ))
lem-σ,,u∘ (el < σ , _ >) (el < u , pu >) δ'@(el < δ , _ >) =
  eq \x -> eq < ref , prf x >
  where
    prf : (x : El _) -> u (δ x) == _ << _ << u (δ (refS << x))
    prf x =
      chain> u (δ x)
         === _ << u (δ (refS << x)) by pu (p─→ δ' (sym (ref<< x)))
         === _ << _ << u (δ (refS << x)) by sym (casttrans _ _ _ _)
      where open module C15 = Chain _==_ (ref {_}) (trans {_})

lem-wk,,vz : {Γ : Con}{A : Type Γ} -> (wk ,, vz) == id {Γ , A}
lem-wk,,vz {Γ}{A} = eq prf
  where
    prf : (x : El (Γ , A)) -> _
    prf (el < x , y >) = ref

