
module cwf where

open import Nat
open import Base
open import univ
open import help

-- Category with Families

infix 40 _─→_
infixl 50 _,_ _,,_
infixl 70 _∘_ _∙_
infixl 60 _/_ _//_

Con : Set
Con = S

_─→_ : Con -> Con -> Set
Γ ─→ Δ = El (pi Γ (K Δ))

p─→ : {Γ Δ : Con}(σ : Γ ─→ Δ){x y : El Γ} -> x == y -> σ # x == σ # y
p─→ σ {x}{y} x=y =
  chain> σ # x
     === refS << σ # y by pFun σ x=y
     === σ # y         by ref<< (σ # y)
  where open module C13 = Chain _==_ (ref {_}) (trans {_})

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
         === σ # (δ # y)      by p─→ σ (p─→ δ x=y)
         === _ << σ # (δ # y) by sym (castref _ _)
      where open module C1 = Chain _==_ (ref {_}) (trans {_})

Type : Con -> Set
Type Γ = Fam Γ

data _=Ty_ {Γ : Con}(A B : Type Γ) : Set where
  eqTy : A =Fam B -> A =Ty B

symTy : {Γ : Con}{A B : Type Γ} -> A =Ty B -> B =Ty A
symTy {Γ}{A}{B} (eqTy A=B) = eqTy (symFam {Γ}{A}{B} A=B)

_/_ : {Γ Δ : Con} -> Type Γ -> (Δ ─→ Γ) -> Type Δ
_/_ {Γ}{Δ} A (el < σ , pσ >) = fam B pB
  where
    B : El Δ -> S
    B x = A ! σ x

    σ' : Δ ─→ Γ
    σ' = el < σ , (\{x}{y} -> pσ) >

    pB : Map _==_ _=S_ B
    pB {x}{y} x=y = pFam A (p─→ σ' x=y)

lem-/id : {Γ : Con}{A : Type Γ} -> A / id =Ty A
lem-/id {Γ}{A} = eqTy \x -> refS

data Elem (Γ : Con)(A : Type Γ) : Set where
  elem : El (pi Γ A) -> Elem Γ A

_=El'_ : {Γ : Con}{A : Type Γ} -> Elem Γ A -> Elem Γ A -> Set
elem u =El' elem v = u == v

data _=El_ {Γ : Con}{A : Type Γ}(u v : Elem Γ A) : Set where
  eqEl : u =El' v -> u =El v

castElem : {Γ : Con}{A B : Type Γ} -> B =Ty A -> Elem Γ A -> Elem Γ B
castElem {Γ}{A}{B} (eqTy B=A) (elem u) = elem (ΓB=ΓA << u)
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
_//_ {Γ}{Δ}{A} (elem t) (el < σ , pσ >) =
    elem (el < tσ , (\{x}{y} -> prf x y) >)
  where
    tσ : (x : El Δ) -> El (A ! σ x)
    tσ x = t # σ x

    σ' : Δ ─→ Γ
    σ' = el < σ , (\{x}{y} -> pσ) >

    prf : (x y : El Δ)(x=y : x == y) -> t # σ x == _ << t # σ y
    prf x y x=y =
      chain> t # σ x
         === _ << t # σ y by pFun t (p─→ σ' x=y)
         === _ << t # σ y by pfi _ _ _
      where open module C3 = Chain _==_ (ref {_}) (trans {_})

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
vz {Γ}{A} = elem (el < f , (\{x}{y} -> pf x y) >)
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
_,,_ {Γ}{Δ}{A} (el < σ , pσ >) (elem (el < u , pu >)) = build δ pδ
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
[_] {Γ}{A} u = id ,, castElem lem-/id u

Π : {Γ : Con}(A : Type Γ)(B : Type (Γ , A)) -> Type Γ
Π {Γ} A B = fam F pF
  where
    F : El Γ -> S
    F x = pi (A ! x) (curryFam B x)

    pF : Map _==_ _=S_ F
    pF {y}{z} y=z = eqS
        < pFam A (sym y=z)
        , (\x -> pFam B (eq < y=z
                            , trans (sym (castref _ _)) (trans<< _ _ _)
                            >
                        )
          )
        >

{- TODO: Prove

  (Π A B) / σ = Π (A / σ) (B / (σ / wk ,, vz))

-}

ƛ : {Γ : Con}{A : Type Γ}{B : Type (Γ , A)} -> Elem (Γ , A) B -> Elem Γ (Π A B)
ƛ {Γ}{A}{B} (elem u) = elem (mkFun f pf)
  where
    f : (x : El Γ) -> El (Π A B ! x)
    f x = el < g , (\{x}{y} -> pg) >
      where
        g : (y : El (A ! x)) -> El (B ! el < x , y >)
        g y = u # el < x , y >

        pg : {y z : El (A ! x)}(y=z : y == z) -> g y == _ << g z
        pg {y}{z} y=z =
          chain> u # el < x , y >
             === _ << u # el < x , z > by pFun u (eqSnd y=z)
             === _ << u # el < x , z > by pfi _ _ _
          where open module C7 = Chain _==_ (ref {_}) (trans {_})

    pf : IsFun {F = Π A B} f
    pf {y}{z} (eqS < Ay=Az , B'=B' >) y=z = eq prf
      where
        prf : (x : El (A ! y)) -> _ == _
        prf x =
          chain> u # el < y , x >
             === _ << u # el < z , _ << x >
              by pFun u (eq < y=z , sym (castref2 _ _ _) >)
             === _ << u # el < z , _ << x > by pfi _ _ _
          where open module C8 = Chain _==_ (ref {_}) (trans {_})

_∙_ : {Γ : Con}{A : Type Γ}{B : Type (Γ , A)}
      (w : Elem Γ (Π A B))(u : Elem Γ A) -> Elem Γ (B / [ u ])
_∙_ {Γ}{A}{B} (elem w) (elem u) = elem (el < f , (\{x}{y} -> pf) >)
  where
    f : (x : El Γ) -> El ((B / [ elem u ]) ! x)
    f x = p u << y
      where
        y : El (B ! el < x , u # x >)
        y = (w # x) # (u # x)

        p : (u : El (pi Γ A)) -> (B / [ elem u ]) ! x =S B ! el < x , u # x >
        p (el < u , pu >) = pFam B (
          chain> el < x , _ << u (refS << x) >
             === el < x , _ << _ << u x > by eqSnd (p<< _ (pu (ref<< _)))
             === el < x , u x >           by eqSnd (castref2 _ _ _)
          )
          where open module C9 = Chain _==_ (ref {_}) (trans {_})

    pf : {x y : El Γ}(x=y : x == y) -> f x == _ << f y
    pf {x}{y} x=y =
      chain> q1 << (w # x) # (u # x)
         === q1 << (q3 << w # y) ## (u # x)
          by p<< q1 (p# (pFun w x=y))
         === q1 << q4 << (w # y) # (q5 << u # x)
          by p<< q1 (distr<<# (w # y) q3)
         === q7 << (w # y) # (q5 << u # x)
          by sym (trans<< q1 q4 _)
         === q7 << q8 << (w # y) # (q5 << q9 << u # y)
          by p<< q7 (pFun (w # y) (p<< q5 (pFun u x=y)))
         === qA << (w # y) # (q5 << q9 << u # y)
          by sym (trans<< q7 q8 _)
         === qA << qB << (w # y) # (u # y)
          by p<< qA (pFun (w # y) (castref2 q5 q9 _))
         === q2 << q6 << (w # y) # (u # y)
          by pfi2 qA q2 qB q6 _
      where
        open module C10 = Chain _==_ (ref {_}) (trans {_})
        q1 = _
        q2 = _
        q3 = _
        q4 = _
        q5 = _
        q6 = _
        q7 = _
        q8 = _
        q9 = _
        qA = _
        qB = _
        infixl 150 _##_
        _##_ = _#_ {F = curryFam B x}

{- TODO: Prove

  (ƛ v) ∙ u = v // [ u ]    (β)
  w = ƛ ((w // wk) ∙ vz)    (η)

  ƛ v // σ = ƛ (v // (σ ∘ wk ,, vz))
  w ∙ u // σ = (w // σ) ∙ (u // σ)

-}
