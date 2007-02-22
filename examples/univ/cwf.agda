
module cwf where

open import Nat
open import Base
open import univ

-- Prelims
infixl 150 _#_

K : {A : S} -> S -> Fam A
K B = fam (\_ -> B) (\{_}{_} _ -> refS)

_#_ : {A : S}{F : Fam A} -> El (pi A F) -> (x : El A) -> El (F ! x)
el < f , _ > # x = f x

pFun : {A : S}{F : Fam A}(f : El (pi A F)){x y : El A}(x=y : x == y) ->
       f # x == pFam F x=y << f # y
pFun (el < f , pf >) x=y = pf x=y

-- Category with Families

infix 40 _─→_
infixl 50 _,_ _,,_
infixl 70 _∘_
infixl 60 _/_ _//_

Con : Set
Con = S

_─→_ : Con -> Con -> Set
Γ ─→ Δ = El (pi Γ (K Δ))

id : {Γ : Con} -> Γ ─→ Γ
id = el < (\x -> x) , (\{x}{y} -> prf x y) >
  where
    prf : (x y : El _)(x=y : x == y) -> x == refS << y
    prf x y x=y =
      chain> x
         === refS << x by sym (ref<< x)
         === refS << y by p<< refS x=y
      where open module C0 = Chain _==_ (ref {_}) (trans {_})

_∘_ : {Γ Δ Θ : Con} -> (Δ ─→ Θ) -> (Γ ─→ Δ) -> Γ ─→ Θ
σ ∘ δ = el < (\x -> σ # (δ # x))
           , (\{x}{y} -> prf x y)
           >
  where
    prf : (x y : El _)(x=y : x == y) -> σ # (δ # x) == _ << σ # (δ # y)
    prf x y x=y =
      chain> σ # (δ # x)
         === refS << σ # (refS << δ # y) by pFun σ (pFun δ x=y)
         === refS << refS << σ # (δ # y) by p<< _ (pFun σ (ref<< _))
         === _ << σ # (δ # y)            by casttrans _ _ _ _
      where open module C1 = Chain _==_ (ref {_}) (trans {_})

{- TODO: Prove

  id ∘ σ = σ ∘ id = σ
  (θ ∘ σ) ∘ δ = Θ ∘ (σ ∘ δ)

-}

Type : Con -> Set
Type Γ = Fam Γ

_=Ty_ : {Γ : Con} -> Type Γ -> Type Γ -> Set
_=Ty_ = _=Fam_

_/_ : {Γ Δ : Con} -> Type Γ -> (Δ ─→ Γ) -> Type Δ
_/_ {Γ}{Δ} A σ = fam B pB
  where
    B : El Δ -> S
    B x = A ! (σ # x)

    pB : Map _==_ _=S_ B
    pB {x}{y} x=y = pFam A (
      chain> σ # x
         === refS << σ # y by pFun σ x=y
         === σ # y         by ref<< _
      )
      where open module C2 = Chain _==_ (ref {_}) (trans {_})

{- TODO: Prove

  A / σ ∘ δ = A / σ / δ

-}

/id : {Γ : Con}{A : Type Γ} -> A / id =Ty A
/id {Γ}{A} x = refS

Elem : (Γ : Con) -> Type Γ -> Set
Elem Γ A = El (pi Γ A)

castElem : {Γ : Con}{A B : Type Γ} -> B =Ty A -> Elem Γ A -> Elem Γ B
castElem {Γ}{A}{B} B=A u = ΓB=ΓA << u
  where
    ΓB=ΓA : pi Γ B =S pi Γ A
    ΓB=ΓA = eqS < refS , Bx=Acx >
      where
        Bx=Acx : (x : El Γ) -> B ! x =S A ! (refS << x)
        Bx=Acx x =
          chain> B ! x
             === A ! x            by B=A x
             === A ! (refS << x)  by pFam A (sym (ref<< x))
          where open module C2-5 = Chain _=S_ refS transS

_//_ : {Γ Δ : Con}{A : Type Γ} -> Elem Γ A -> (σ : Δ ─→ Γ) -> Elem Δ (A / σ)
_//_ {Γ}{Δ}{A} t σ =
    el < tσ , (\{x}{y} -> prf x y) >
  where
    tσ : (x : El Δ) -> El (A ! (σ # x))
    tσ x = t # (σ # x)

    prf : (x y : El Δ)(x=y : x == y) -> t # (σ # x) == _ << t # (σ # y)
    prf x y x=y =
      chain> t # (σ # x)
         === _ << t # (_ << σ # y) by pFun t (pFun σ x=y)
         === _ << _ << t # (σ # y) by p<< _ (pFun t (castref _ _))
         === _ << t # (σ # y)      by casttrans _ _ _ _
      where open module C3 = Chain _==_ (ref {_}) (trans {_})

{- TODO: Prove

  u // id    = u
  u // σ ∘ δ = u // σ // δ

-}

_,_ : (Γ : Con)(A : Type Γ) -> Con
Γ , A = sigma Γ A

wk : {Γ : Con}{A : Type Γ} -> Γ , A ─→ Γ
wk {Γ}{A} = el < f , (\{x}{y} -> pf x y) >
  where
    f : El (Γ , A) -> El Γ
    f (el < x , _ >) = x

    pf : (x y : El (Γ , A))(x=y : x == y) -> f x == _ << f y
    pf (el < x , _ >) (el < y , _ >) (eq < x=y , _ >) =
      chain> x
         === y      by x=y
         === _ << y by sym (castref _ _)
      where open module C4 = Chain _==_ (ref {_}) (trans {_})

vz : {Γ : Con}{A : Type Γ} -> Elem (Γ , A) (A / wk)
vz {Γ}{A} = el < f , (\{x}{y} -> pf x y) >
  where
    f : (x : El (Γ , A)) -> El ((A / wk) ! x)
    f (el < _ , z >) = z

    pf : (x y : El (Γ , A))(x=y : x == y) -> f x == _ << f y
    pf (el < _ , x >)(el < _ , y >)(eq < _ , x=y >) =
      chain> x
         === _ << y by x=y
         === _ << y by pfi _ _ _
      where open module C5 = Chain _==_ (ref {_}) (trans {_})

_,,_ : {Γ Δ : Con}{A : Type Γ}(σ : Δ ─→ Γ)(u : Elem Δ (A / σ)) -> Δ ─→ Γ , A
_,,_ {Γ}{Δ}{A} (el < σ , pσ >) (el < u , pu >) = build δ pδ
  where
    -- We need to generalise to be able to infer the proof of Γ, A =S Γ, A
    Ok : (f : El Δ -> El (Γ , A)) -> Set
    Ok f = (x y : El Δ)(p : Γ , A =S Γ , A)(x=y : x == y) -> f x == p << f y

    build : (f : El Δ -> El (Γ , A)) -> Ok f -> Δ ─→ Γ , A
    build f p = el < f , (\{x}{y} -> p x y _) >

    δ : El Δ -> El (Γ , A)
    δ x = el {Γ , A} < σ x , u x >

    pδ : Ok δ
    pδ x y (eqS < Γ=Γ , A=A >) x=y =
      eq < σx=cσy , ux=ccuy >
      where
        σx=cσy = trans (pσ x=y) (pfi _ _ _)
        ux=ccuy =
          chain> u x
             === _ << u y      by pu x=y
             === _ << _ << u y by sym (casttrans _ _ _ _)
          where open module C6 = Chain _==_ (ref {_}) (trans {_})

{- TODO: Prove

  wk ∘ (σ ,, u) = σ
  vz / (σ ,, u) = u

  (σ ,, u) ∘ δ  = (σ ∘ δ ,, u)
  wk ,, vz      = id

-}

[_] : {Γ : Con}{A : Type Γ} -> Elem Γ A -> Γ ─→ Γ , A
[_] {Γ}{A} u = id ,, castElem /id u

