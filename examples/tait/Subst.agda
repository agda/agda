
module Subst where

open import Prelude
open import Lambda

infix 100 _[_] _[_:=_] _↑
infixl 100 _↑_ _↓ˣ_
infixl 60 _-_

_-_ : {τ : Type}(Γ : Ctx) -> Var Γ τ -> Ctx
ε     - ()
Γ , τ - vz   = Γ
Γ , τ - vs x = (Γ - x) , τ

wkˣ : {Γ : Ctx}{σ τ : Type}
      (x : Var Γ σ) -> Var (Γ - x) τ -> Var Γ τ
wkˣ vz     y      = vs y
wkˣ (vs x) vz     = vz
wkˣ (vs x) (vs y) = vs (wkˣ x y)

wk : {Γ : Ctx}{σ τ : Type}
     (x : Var Γ σ) -> Term (Γ - x) τ -> Term Γ τ
wk x (var y) = var (wkˣ x y)
wk x (s • t) = wk x s • wk x t
wk x (λ t)   = λ wk (vs x) t 

_↑ : {Γ : Ctx}{σ τ : Type} -> Term Γ τ -> Term (Γ , σ) τ
t ↑ = wk vz t

_↑_ : {Γ : Ctx}{τ : Type} -> Term Γ τ -> (Δ : Ctx) -> Term (Γ ++ Δ) τ
t ↑ ε       = t
t ↑ (Δ , σ) = (t ↑ Δ) ↑

data Cmpˣ {Γ : Ctx}{τ : Type}(x : Var Γ τ) :
          {σ : Type} -> Var Γ σ -> Set where
  same : Cmpˣ x x
  diff : {σ : Type}(y : Var (Γ - x) σ) -> Cmpˣ x (wkˣ x y)

_≟_ : {Γ : Ctx}{σ τ : Type}(x : Var Γ σ)(y : Var Γ τ) -> Cmpˣ x y
vz   ≟ vz   = same
vz   ≟ vs y = diff y
vs x ≟ vz   = diff vz
vs x ≟ vs y with x ≟ y
vs x ≟ vs .x         | same   = same
vs x ≟ vs .(wkˣ x y) | diff y = diff (vs y)

_[_:=_] : {Γ : Ctx}{σ τ : Type} ->
         Term Γ σ -> (x : Var Γ τ) -> Term (Γ - x) τ ->
         Term (Γ - x) σ
var y   [ x := u ] with x ≟ y
var .x         [ x := u ] | same = u
var .(wkˣ x y) [ x := u ] | diff y = var y
(s • t) [ x := u ] = s [ x := u ] • t [ x := u ]
(λ t)   [ x := u ] = λ t [ vs x := u ↑ ]

_[_] : {Γ : Ctx}{σ τ : Type} ->
       Term (Γ , τ) σ -> Term Γ τ -> Term Γ σ
t [ u ] = t [ vz := u ]

_↓ˣ_ : {Γ : Ctx}{σ τ : Type}
       (y : Var Γ σ)(x : Var (Γ - y) τ) -> Var (Γ - wkˣ y x) σ
vz   ↓ˣ x    = vz
vs y ↓ˣ vz   = y
vs y ↓ˣ vs x = vs (y ↓ˣ x)

lem-commute-minus :
  {Γ : Ctx}{σ τ : Type}(y : Var Γ σ)(x : Var (Γ - y) τ) ->
  Γ - y - x ≡ Γ - wkˣ y x - (y ↓ˣ x)
lem-commute-minus vz     x      = refl
lem-commute-minus (vs y) vz     = refl
lem-commute-minus (vs {Γ} y) (vs x) with Γ - y - x | lem-commute-minus y x
... | ._ | refl = refl


Lem-wk-[] :
      {Γ : Ctx}{τ σ ρ : Type}
      (y : Var Γ τ)
      (x : Var (Γ - y) σ)
      (t : Term (Γ - wkˣ y x) ρ)
      (u : Term (Γ - y - x) τ) -> Set
Lem-wk-[] {Γ}{τ}{σ}{ρ} y x t u =
    wk (wkˣ y x) t [ y := wk x u ]
    ≡ wk x t[u']'
  where
    u' : Term (Γ - wkˣ y x - y ↓ˣ x) τ
    u' = subst (\Δ -> Term Δ τ) (sym (lem-commute-minus y x)) u

    t[u']' : Term (Γ - y - x) ρ
    t[u']' = subst (\Δ -> Term Δ ρ) (lem-commute-minus y x)
             (t [ y ↓ˣ x := u' ])

postulate
 lem-wk-[] : {Γ : Ctx}{σ τ ρ : Type}
             (y : Var Γ τ)(x : Var (Γ - y) σ)
             (t : Term (Γ - wkˣ y x) ρ){u : Term (Γ - y - x) τ} ->
             Lem-wk-[] y x t u
{-
lem-wk-[] y x (var z) = {! !}
lem-wk-[] y x (t • u) = {! !}
lem-wk-[] y x (λ t)   = {! !}
-}

lem-wk-[]' : {Γ : Ctx}{σ τ ρ : Type}
            (x : Var Γ σ)(t : Term (Γ - x , ρ) τ){u : Term (Γ - x) ρ} ->
            wk x (t [ vz := u ]) ≡ wk (vs x) t [ vz := wk x u ]
lem-wk-[]' x t = sym (lem-wk-[] vz x t)