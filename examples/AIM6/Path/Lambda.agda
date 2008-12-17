module Lambda where

open import Prelude
open import Star
open import Examples
open import Modal

-- Environments

record TyAlg (ty : Set) : Set where
  field
    nat : ty
    _⟶_ : ty -> ty -> ty

data Ty : Set where
  <nat> : Ty
  _<⟶>_ : Ty -> Ty -> Ty

freeTyAlg : TyAlg Ty
freeTyAlg = record { nat = <nat>; _⟶_ = _<⟶>_ }

termTyAlg : TyAlg True
termTyAlg = record { nat = _; _⟶_ = \_ _ -> _ }

record TyArrow {ty₁ ty₂ : Set}(T₁ : TyAlg ty₁)(T₂ : TyAlg ty₂) : Set where
  field
    apply   : ty₁ -> ty₂
    respNat : apply (TyAlg.nat T₁) == TyAlg.nat T₂
    resp⟶   : forall {τ₁ τ₂} ->
              apply (TyAlg._⟶_ T₁ τ₁ τ₂) == TyAlg._⟶_ T₂ (apply τ₁) (apply τ₂)

_=Ty=>_ : {ty₁ ty₂ : Set}(T₁ : TyAlg ty₁)(T₂ : TyAlg ty₂) -> Set
_=Ty=>_ = TyArrow

!Ty : {ty : Set}{T : TyAlg ty} -> T =Ty=> termTyAlg
!Ty = record { apply   = !
             ; respNat = refl
             ; resp⟶   = refl
             }

Ctx : Set
Ctx = List Ty

Var : {ty : Set} -> List ty -> ty -> Set
Var Γ τ = Any (_==_ τ) Γ

vzero : {τ : Ty} {Γ : Ctx} -> Var (τ • Γ) τ
vzero = done refl • ε

vsuc : {σ τ : Ty} {Γ : Ctx} -> Var Γ τ -> Var (σ • Γ) τ
vsuc v = step • v

module Term {ty : Set}(T : TyAlg ty) where

  private open module TT = TyAlg T

  data Tm : List ty -> ty -> Set where
    var : forall {Γ τ}   -> Var Γ τ -> Tm Γ τ
    zz  : forall {Γ}     -> Tm Γ nat
    ss  : forall {Γ}     -> Tm Γ (nat ⟶ nat)
    ƛ   : forall {Γ σ τ} -> Tm (σ • Γ) τ -> Tm Γ (σ ⟶ τ)
    _$_ : forall {Γ σ τ} -> Tm Γ (σ ⟶ τ) -> Tm Γ σ -> Tm Γ τ

module Eval where

 private open module TT = Term freeTyAlg

 ty⟦_⟧ : Ty -> Set
 ty⟦ <nat>   ⟧ = Nat
 ty⟦ σ <⟶> τ ⟧ = ty⟦ σ ⟧ -> ty⟦ τ ⟧

 Env : Ctx -> Set
 Env = All ty⟦_⟧

 _[_] : forall {Γ τ} -> Env Γ -> Var Γ τ -> ty⟦ τ ⟧
 ρ [ x ] with lookup x ρ
 ...     | result _ refl v = v

 ⟦_⟧_ : forall {Γ τ} -> Tm Γ τ -> Env Γ -> ty⟦ τ ⟧
 ⟦ var x ⟧ ρ = ρ [ x ]
 ⟦ zz    ⟧ ρ = zero
 ⟦ ss    ⟧ ρ = suc
 ⟦ ƛ t   ⟧ ρ = \x -> ⟦ t ⟧ (check x • ρ)
 ⟦ s $ t ⟧ ρ = (⟦ s ⟧ ρ) (⟦ t ⟧ ρ)

module MoreExamples where

  private open module TT = TyAlg freeTyAlg
  private open module Tm = Term freeTyAlg
  open Eval

  tm-one : Tm ε nat
  tm-one = ss $ zz

  tm-id : Tm ε (nat ⟶ nat)
  tm-id = ƛ (var (done refl • ε))

  tm    : Tm ε nat
  tm    = tm-id $ tm-one

  tm-twice : Tm ε ((nat ⟶ nat) ⟶ (nat ⟶ nat))
  tm-twice = ƛ (ƛ (f $ (f $ x)))
    where Γ : Ctx
          Γ = nat • (nat ⟶ nat) • ε
          f : Tm Γ (nat ⟶ nat)
          f = var (vsuc vzero)
          x : Tm Γ nat
          x = var vzero

  sem : {τ : Ty} -> Tm ε τ -> ty⟦ τ ⟧
  sem e = ⟦ e ⟧ ε

  one : Nat
  one = sem tm

  twice : (Nat -> Nat) -> (Nat -> Nat)
  twice = sem tm-twice
