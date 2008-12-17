
module Subst where

open import Prelude
open import Lambda

infix 100 _[_] _[_:=_] _↑
infixl 100 _↑_ _↑ˢ_ _↑ˣ_ _↓ˣ_
infixl 60 _-_

{-
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
wk x (ƛ t)   = ƛ wk (vs x) t

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
(ƛ t)   [ x := u ] = ƛ t [ vs x := u ↑ ]
-}

infix 30 _─⟶_
infixl 90 _/_

_─⟶_ : Ctx -> Ctx -> Set
Γ ─⟶ Δ = Terms Γ Δ

idS : forall {Γ} -> Γ ─⟶ Γ
idS = tabulate var

infixr 80 _∘ˢ_

[_] : forall {Γ σ  } -> Term Γ σ -> Γ ─⟶ Γ , σ
[ t ] = idS ◄ t

wkS : forall {Γ Δ τ} -> Γ ─⟶ Δ -> Γ , τ ─⟶ Δ
wkS ∅       = ∅
wkS (θ ◄ t) = wkS θ ◄ wk t

_↑ : forall {Γ Δ τ} -> (Γ ─⟶ Δ) -> Γ , τ ─⟶ Δ , τ
θ ↑ = wkS θ ◄ vz

_/_ : forall {Γ Δ τ} -> Term Δ τ -> Γ ─⟶ Δ -> Term Γ τ
vz      / (θ ◄ u) = u
wk t    / (θ ◄ u) = t / θ
(s • t) / θ       = s / θ • t / θ
(ƛ t)   / θ       = ƛ t / θ ↑

_∘ˢ_ : forall {Γ Δ Θ} -> Δ ─⟶ Θ -> Γ ─⟶ Δ -> Γ ─⟶ Θ
∅       ∘ˢ θ = ∅
(δ ◄ t) ∘ˢ θ = δ ∘ˢ θ ◄ t / θ

inj : forall {Γ Δ τ} Θ -> Term Γ τ -> Γ ─⟶ Δ ++ Θ -> Γ ─⟶ Δ , τ ++ Θ
inj ε       t θ       = θ ◄ t
inj (Θ , σ) t (θ ◄ u) = inj Θ t θ ◄ u

[_⟵_] : forall {Γ τ} Δ -> Term (Γ ++ Δ) τ -> Γ ++ Δ ─⟶ Γ , τ ++ Δ
[ Δ ⟵ t ] = inj Δ t idS

_↑_ : forall {Γ σ} -> Term Γ σ -> (Δ : Ctx) -> Term (Γ ++ Δ) σ
t ↑ ε       = t
t ↑ (Δ , τ) = wk (t ↑ Δ)

_↑ˢ_ : forall {Γ Δ} -> Terms Γ Δ -> (Θ : Ctx) -> Terms (Γ ++ Θ) Δ
∅        ↑ˢ Θ = ∅
(ts ◄ t) ↑ˢ Θ = ts ↑ˢ Θ ◄ t ↑ Θ

_↑ˣ_ : forall {Γ τ} -> Var Γ τ -> (Δ : Ctx) -> Var (Γ ++ Δ) τ
x ↑ˣ ε       = x
x ↑ˣ (Δ , σ) = vsuc (x ↑ˣ Δ)

lem-var-↑ˣ : forall {Γ τ}(x : Var Γ τ)(Δ : Ctx) ->
             var (x ↑ˣ Δ) ≡ var x ↑ Δ
lem-var-↑ˣ x ε       = refl
lem-var-↑ˣ x (Δ , σ) = cong wk (lem-var-↑ˣ x Δ)

{- Not true!
lem-•-↑ : forall {Γ σ τ}(t : Term Γ (σ ⟶ τ))(u : Term Γ σ) Δ ->
          (t ↑ Δ) • (u ↑ Δ) ≡ (t • u) ↑ Δ
lem-•-↑ t u ε       = refl
lem-•-↑ t u (Δ , δ) = {! !}

lem-•ˢ-↑ : forall {Γ Θ τ}(t : Term Γ (Θ ⇒ τ))(ts : Terms Γ Θ) Δ ->
           (t ↑ Δ) •ˢ (ts ↑ˢ Δ) ≡ (t •ˢ ts) ↑ Δ
lem-•ˢ-↑ t ∅        Δ = refl
lem-•ˢ-↑ t (u ◄ us) Δ = {! !}
-}

{-
_[_] : {Γ : Ctx}{σ τ : Type} ->
       Term (Γ , τ) σ -> Term Γ τ -> Term Γ σ
t [ u ] = t / [ u ]
-}

{-
vz      [ u ] = u
wk t    [ u ] = {! !}
(s • t) [ u ] = {! !}
(ƛ_ {τ = ρ} t)   [ u ] = ƛ {! !}
-}

{-
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
lem-wk-[] y x (ƛ t)   = {! !}
-}

lem-wk-[]' : {Γ : Ctx}{σ τ ρ : Type}
            (x : Var Γ σ)(t : Term (Γ - x , ρ) τ){u : Term (Γ - x) ρ} ->
            wk x (t [ vz := u ]) ≡ wk (vs x) t [ vz := wk x u ]
lem-wk-[]' x t = sym (lem-wk-[] vz x t)

-}