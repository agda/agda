
-- A Typed version of a subset of Landin's ISWIM from "The Next 700 Programming
-- Languages"

module ISWIM where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}
{-# BUILTIN NATPLUS _+_  #-}

data Bool : Set where
  true  : Bool
  false : Bool

module Syntax where

  infixl 100 _∙_
  infixl 80 _WHERE_ _PP_
  infixr 60 _─→_
  infixl 40 _,_

  data Type : Set where
    nat  : Type
    bool : Type
    _─→_ : Type -> Type -> Type

  data Context : Set where
    ε   : Context
    _,_ : Context -> Type -> Context

  data Var : Context -> Type -> Set where
    vz : {Γ : Context}{τ : Type}            -> Var (Γ , τ) τ
    vs : {Γ : Context}{σ τ : Type} -> Var Γ τ -> Var (Γ , σ) τ

  data Expr (Γ : Context) : Type -> Set where
    var   : {τ : Type} -> Var Γ τ -> Expr Γ τ
    litNat  : Nat -> Expr Γ nat
    litBool : Bool -> Expr Γ bool
    plus    : Expr Γ (nat ─→ nat ─→ nat)
    if      : {τ : Type} -> Expr Γ (bool ─→ τ ─→ τ ─→ τ)
    _∙_           : {σ τ : Type} -> Expr Γ (σ ─→ τ) -> Expr Γ σ -> Expr Γ τ
    _WHERE_ : {σ τ ρ : Type} -> Expr (Γ , σ ─→ τ) ρ -> Expr (Γ , σ) τ -> Expr Γ ρ
    _PP_    : {σ τ ρ : Type} -> Expr (Γ , σ ─→ τ) ρ -> Expr (Γ , σ) ρ -> Expr Γ ρ

  -- ƛ x. e = f where f x = e
  ƛ : {Γ : Context}{σ τ : Type} -> Expr (Γ , σ) τ -> Expr Γ (σ ─→ τ)
  ƛ e = var vz WHERE e

module Cont (R : Set) where

  C : Set -> Set
  C a = (a -> R) -> R

  callcc : {a : Set} -> (({b : Set} -> a -> C b) -> C a) -> C a
  callcc {a} g = \k -> g (\x _ -> k x) k

  return : {a : Set} -> a -> C a
  return x = \k -> k x

  infixr 10 _>>=_

  _>>=_ : {a b : Set} -> C a -> (a -> C b) -> C b
  (m >>= k) ret = m \x -> k x ret

module Semantics (R : Set) where

  open module C = Cont R
  open Syntax

  infix 60 _!_
  infixl 40 _||_

  ⟦_⟧type : Type -> Set

  ⟦_⟧type' : Type -> Set
  ⟦ nat    ⟧type' = Nat
  ⟦ bool   ⟧type' = Bool
  ⟦ σ ─→ τ ⟧type' = ⟦ σ ⟧type' -> ⟦ τ ⟧type

  ⟦ τ ⟧type = C ⟦ τ ⟧type'

  data ⟦_⟧ctx : Context -> Set where
    ★    : ⟦ ε ⟧ctx
    _||_ : {Γ : Context}{τ : Type} -> ⟦ Γ ⟧ctx -> ⟦ τ ⟧type' -> ⟦ Γ , τ ⟧ctx

  _!_ : {Γ : Context}{τ : Type} -> ⟦ Γ ⟧ctx -> Var Γ τ -> ⟦ τ ⟧type'
  ★      ! ()
  (ρ || v) ! vz   = v
  (ρ || v) ! vs x = ρ ! x

  ⟦_⟧ : {Γ : Context}{τ : Type} -> Expr Γ τ -> ⟦ Γ ⟧ctx -> ⟦ τ ⟧type
  ⟦ var x   ⟧ ρ = return (ρ ! x)
  ⟦ litNat n        ⟧ ρ = return n
  ⟦ litBool b       ⟧ ρ = return b
  ⟦ plus    ⟧ ρ = return \n -> return \m -> return (n + m)
  ⟦ f ∙ e ⟧ ρ = ⟦ e ⟧ ρ >>= \v ->
                    ⟦ f ⟧ ρ >>= \w ->
                    w v
  ⟦ e WHERE f ⟧ ρ = ⟦ e ⟧ (ρ || (\x -> ⟦ f ⟧ (ρ || x)))
  ⟦ e PP f  ⟧ ρ = callcc \k ->
                    let throw = \x -> ⟦ f ⟧ (ρ || x) >>= k
                    in  ⟦ e ⟧ (ρ || throw)
  ⟦ if        ⟧ ρ = return \x -> return \y -> return \z -> return (iff x y z)
    where
      iff : {A : Set} -> Bool -> A -> A -> A
      iff true  x y = x
      iff false x y = y

module Test where

  open Syntax
  open module C = Cont Nat
  open module S = Semantics Nat

  run : Expr ε nat -> Nat
  run e = ⟦ e ⟧ ★ \x -> x

  -- 1 + 1
  two : Expr ε nat
  two = plus ∙ litNat 1 ∙ litNat 1

  -- f 1 + f 2 where f x = x
  three : Expr ε nat
  three = plus ∙ (var vz ∙ litNat 1) ∙ (var vz ∙ litNat 2) WHERE var vz

  -- 1 + f 1 where pp f x = x
  one : Expr ε nat
  one = plus ∙ litNat 1 ∙ (var vz ∙ litNat 1) PP var vz

open Test

data _==_ {a : Set}(x : a) : a -> Set where
  refl : x == x

twoOK : run two == 2
twoOK = refl

threeOK : run three == 3
threeOK = refl

oneOK : run one == 1
oneOK = refl

open Cont
open Syntax
open Semantics

