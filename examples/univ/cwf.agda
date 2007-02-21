
module cwf where

open import Nat
open import Base
open import univ

infix 40 _─→_
infixl 80 _,_ _,,_
infixl 60 _∘_
infixl 70 _/_ _//_

K : {A : S} -> S -> Fam A
K B = fam (\_ -> B) (\{_}{_} _ -> refS)

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
      where open module C = Chain _==_ (ref {_}) (trans {_})

_∘_ : {Γ Δ Θ : Con} -> (Δ ─→ Θ) -> (Γ ─→ Δ) -> Γ ─→ Θ
el < f , pf > ∘ el < g , pg > =
  el < (\x -> f (g x))
     , (\{x}{y} -> prf x y)
     >
  where
    prf : (x y : El _)(x=y : x == y) -> f (g x) == _ << f (g y)
    prf x y x=y =
      chain> f (g x)
         === refS << f (refS << g y) by pf (pg x=y)
         === refS << refS << f (g y) by p<< _ (pf (ref<< _))
         === _ << f (g y)            by casttrans _ _ _ _
      where open module C = Chain _==_ (ref {_}) (trans {_})

Type : Con -> Set
Type Γ = Fam Γ

_/_ : {Γ Δ : Con} -> Type Γ -> (Δ ─→ Γ) -> Type Δ
_/_ {Γ}{Δ} A (el < σ , pσ >) = fam B pB
  where
    B : El Δ -> S
    B x = A ! σ x

    pB : Map _==_ _=S_ B
    pB {x}{y} x=y = pFam A (
      chain> σ x
         === refS << σ y by pσ x=y
         === σ y         by ref<< _
      )
      where open module C = Chain _==_ (ref {_}) (trans {_})

  -- fam (\x -> A ! (σ << x)) (\{x}{y} x=y -> pFam A (p<< σ x=y))

Elem : (Γ : Con) -> Type Γ -> Set
Elem Γ A = El (pi Γ A)

_//_ : {Γ Δ : Con}{A : Type Γ} -> Elem Γ A -> (σ : Δ ─→ Γ) -> Elem Δ (A / σ)
_//_ {Γ}{Δ}{A} (el < t , pt >) (el < σ , pσ >) =
    el < tσ , (\{x}{y} -> prf x y) >
  where
    tσ : (x : El Δ) -> El (A ! σ x)
    tσ x = t (σ x)

    prf : (x y : El Δ)(x=y : x == y) -> t (σ x) == _ << t (σ y)
    prf x y x=y =
      chain> t (σ x)
         === _ << t (_ << σ y) by pt (pσ x=y)
         === _ << _ << t (σ y) by p<< _ (pt (castref _ _))
         === _ << t (σ y)      by casttrans _ _ _ _
      where open module C' = Chain _==_ (ref {_}) (trans {_})

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
      where open module C = Chain _==_ (ref {_}) (trans {_})

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
      where open module C' = Chain _==_ (ref {_}) (trans {_})

_,,_ : {Γ Δ : Con}{A : Type Γ}(σ : Δ ─→ Γ)(u : Elem Δ (A / σ)) -> Δ ─→ Γ , A
_,,_ {Γ}{Δ}{A} (el < σ , pσ >) (el < u , pu >) = build δ pδ
  where
    Good : (f : El Δ -> El (Γ , A)) -> Set
    Good f = (x y : El Δ)(p : Γ , A =S Γ , A)(x=y : x == y) -> f x == p << f y

    build : (f : El Δ -> El (Γ , A)) -> Good f -> Δ ─→ Γ , A
    build f p = el < f , (\{x}{y} -> p x y ?) >

    δ : El Δ -> El (Γ , A)
    δ x = el {Γ , A} < σ x , u x >

    pδ : Good δ
    pδ x y (eqS < Γ=Γ , A=A >) x=y =
      eq < σx=cσy , ux=ccuy >
      where
        σx=cσy = trans (pσ x=y) (pfi _ _ _)
        ux=ccuy =
          chain> u x
             === _ << u y      by pu x=y
             === _ << _ << u y by sym (casttrans _ _ _ _)
          where open module C'' = Chain _==_ (ref {_}) (trans {_})

