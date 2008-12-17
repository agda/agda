
module proofs where

open import univ
open import cwf
open import Base
open import Nat
open import help

{-
lem-id∘ : {Γ Δ : Con}(σ : Γ ─→ Δ) -> id ∘ σ == σ
lem-id∘ (el < σ , pσ >) = eq \x -> ref

lem-∘id : {Γ Δ : Con}(σ : Γ ─→ Δ) -> σ ∘ id == σ
lem-∘id (el < σ , pσ >) = eq \x -> ref

lem-∘assoc : {Γ Δ Θ Ξ : Con}(σ : Θ ─→ Ξ)(δ : Δ ─→ Θ)(θ : Γ ─→ Δ) ->
             (σ ∘ δ) ∘ θ == σ ∘ (δ ∘ θ)
lem-∘assoc (el < σ , pσ >) (el < δ , pδ >) (el < θ , pθ >) = eq \x -> ref
-}

lem-/∘ : {Γ Δ Θ : Con}(A : Type Γ)(σ : Δ ─→ Γ)(δ : Θ ─→ Δ) ->
         A / σ ∘ δ =Ty A / σ / δ
lem-/∘ A (el < _ , _ >) (el < _ , _ >) = eqTy \x -> refS

{-
lem-//id : {Γ : Con}{A : Type Γ}{u : Elem Γ A} -> u // id =El castElem lem-/id u
lem-//id {Γ}{A}{elem (el < u , pu >)} = eqEl (eq prf)
  where
    prf : (x : El Γ) -> _
    prf x =
      chain> u x
         === _ << u (refS << x) by pu (sym (ref<< x))
         === _ << u (refS << x) by pfi _ _ _
      where open module C11 = Chain _==_ (ref {_}) (trans {_})

lem-//∘ : {Γ Δ Θ : Con}{A : Type Γ}(u : Elem Γ A)(σ : Δ ─→ Γ)(δ : Θ ─→ Δ) ->
          u // σ ∘ δ =El castElem (lem-/∘ A σ δ) (u // σ // δ)
lem-//∘ {Γ}{Δ}{Θ} (elem (el < u , pu >)) σ'@(el < σ , _ >) δ'@(el < δ , _ >) = eqEl (eq prf)
  where
    prf : (x : El Θ) -> _
    prf x =
      chain> u (σ (δ x))
         === _ << u (σ (δ (refS << x))) by pu (p─→ σ' (p─→ δ' (sym (ref<< x))))
         === _ << u (σ (δ (refS << x))) by pfi _ _ _
      where open module C12 = Chain _==_ (ref {_}) (trans {_})

lem-wk∘σ,,u : {Γ Δ : Con}{A : Type Γ}(σ : Δ ─→ Γ)(u : Elem Δ (A / σ)) ->
              wk ∘ (σ ,, u) == σ
lem-wk∘σ,,u (el < σ , pσ >) (elem (el < u , pu >)) = eq \x -> ref

lem-/wk∘σ,,u : {Γ Δ : Con}(A : Type Γ)(σ : Δ ─→ Γ)(u : Elem Δ (A / σ)) ->
               A / wk / (σ ,, u) =Ty A / σ
lem-/wk∘σ,,u A (el < σ , pσ >) (elem (el < u , pu >)) = eqTy \x -> refS

lem-vz/σ,,u : {Γ Δ : Con}{A : Type Γ}(σ : Δ ─→ Γ)(u : Elem Δ (A / σ)) ->
              vz // (σ ,, u) =El castElem (lem-/wk∘σ,,u A σ u) u
lem-vz/σ,,u (el < σ , pσ >) (elem (el < u , pu >)) = eqEl (eq \x -> prf x)
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
lem-σ,,u∘ (el < σ , _ >) (elem (el < u , pu >)) δ'@(el < δ , _ >) =
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
-}

lem-Π/ : {Γ Δ : Con}{A : Type Γ}(B : Type (Γ , A))(σ : Δ ─→ Γ) ->
         Π A B / σ =Ty Π (A / σ) (B / (σ ∘ wk ,, castElem (lem-/∘ A σ wk) vz))
lem-Π/ B (el < σ , pσ >) =
  eqTy \x -> eqS < refS , (\y -> pFam B (eq < ref , prf x y >)) >
  where
    postulate prf : (x : El _)(y : El _) -> y == _ << _ << _ << _ << y
--     prf x y =
--       chain> y
--          === _ << _ << y           by sym (castref2 _ _ y)
--          === _ << _ << _ << y      by trans<< _ _ _
--          === _ << _ << _ << _ << y by trans<< _ _ _
--       where open module C16 = Chain _==_ (ref {_}) (trans {_})

{-
lem-β : {Γ : Con}{A : Type Γ}{B : Type (Γ , A)}
	(v : Elem (Γ , A) B)(u : Elem Γ A) ->
	(ƛ v) ∙ u =El v // [ u ]
lem-β {Γ}{A}{B} (elem (el < v , pv >)) (elem (el < u , pu >)) = eqEl (eq \x -> prf x _ _)
  where
    prf : (x : El Γ)(q : _ =S _)(p : _ =S _) ->
	  p << v (el < x , u x >) == v (el < x , q << u (refS << x) >)
    prf x q p =
      chain> p << v (el < x , u x >)
	 === p << q0 << v (el < x , q1 << u (refS << x) >)
	  by p<< p (pv (eqSnd (pu (sym (ref<< x)))))
	 === q2 << v (el < x , q1 << u (refS << x) >)
	  by sym (trans<< p q0 _)
	 === q2 << q3 << v (el < x , q << u (refS << x) >)
	  by p<< q2 (pv (eqSnd (pfi q1 q _)))
	 === v (el < x , q << u (refS << x) >)
	  by castref2 q2 q3 _
      where
	open module C17 = Chain _==_ (ref {_}) (trans {_})
	q0 = _
	q1 = _
	q2 = _
	q3 = _

-}
