
open import Prelude

module Typed
  (Name   : Set)

  -- Data stuff
  (Datatype : Name -> List (List Name))

  -- Effect stuff
  (Effect : Set)
  (_⊆_    : Effect -> Effect -> Set)
  (Monad  : Effect -> Set -> Set)
  (return : forall {M A} -> A -> Monad M A)
  (map    : forall {M A B} -> (A -> B) -> Monad M A -> Monad M B)
  (join   : forall {M A} -> Monad M (Monad M A) -> Monad M A)
  (morph  : forall {M N} -> M ⊆ N -> (A : Set) -> Monad M A -> Monad N A)
  where

_=<<_ : forall {M A B} -> (A -> Monad M B) -> Monad M A -> Monad M B
k =<< m = join (map k m)

_>>=_ : forall {M A B} -> Monad M A -> (A -> Monad M B) -> Monad M B
m >>= k = k =<< m

infixl 50 _<*>_

_<*>_ : forall {M A B} -> Monad M (A -> B) -> Monad M A -> Monad M B
f <*> x = f >>= \f -> x >>= \x -> return (f x)

infixr 80 _⟶_
infix 100 [_]_

data VTy : Set

data CTy : Set where
  _⟶_  : VTy -> CTy -> CTy
  [_]_ : Effect -> VTy -> CTy

data VTy where
  ⟨_⟩   : CTy -> VTy
  TyCon : Name -> VTy

Cxt = List VTy

data ExC : Effect -> Cxt -> CTy -> Set
data InV : Effect -> Cxt -> VTy -> Set

data InC : Cxt -> CTy -> Set where

  ƛ_  : forall {V C Γ} ->
        InC (Γ ◄ V) C -> InC Γ (V ⟶ C)

  exC : forall {M N Γ V} ->
        ExC M Γ ([ N ] V) -> N ⊆ M -> InC Γ ([ M ] V)

  inV : forall {M Γ V} ->
        InV M Γ V -> InC Γ ([ M ] V)

InDs : Effect -> Cxt -> List Name -> Set

data InV where

  ⟪_⟫ : forall {M Γ C} -> InC Γ C -> InV M Γ ⟨ C ⟩

  ⟦_⟧ : forall {M Γ V} -> InC Γ ([ M ] V) -> InV M Γ V

  con : forall {M Γ D args} ->
        args ∈ Datatype D -> InDs M Γ args -> InV M Γ (TyCon D)

InDs M Γ = Box (\D -> InV M Γ (TyCon D))

data ExC where

  var : forall {M Γ V} -> V ∈ Γ -> ExC M Γ ([ M ] V)

  _•_ : forall {M Γ V C} ->
        ExC M Γ (V ⟶ C) -> InV M Γ V -> ExC M Γ C

Els : _

data El : Name -> Set where
  el : forall {args D} -> args ∈ Datatype D -> Els args -> El D

Els = Box El

VTy⟦_⟧ : VTy -> Set

CTy⟦_⟧ : CTy -> Set
CTy⟦ V ⟶ C   ⟧ = VTy⟦ V ⟧ -> CTy⟦ C ⟧
CTy⟦ [ M ] V ⟧ = Monad M VTy⟦ V ⟧


VTy⟦ ⟨ C ⟩   ⟧ = CTy⟦ C ⟧
VTy⟦ TyCon D ⟧ = El D

Env = Box VTy⟦_⟧

inC⟦_⟧ : forall {Γ C} -> InC Γ C -> Env Γ -> CTy⟦ C ⟧

inDs⟦_⟧ : forall {M Γ Ds} ->
          InDs M Γ Ds -> Env Γ -> Monad M (Els Ds)

inV⟦_⟧ : forall {M Γ V} -> InV M Γ V -> Env Γ -> Monad M VTy⟦ V ⟧
inV⟦ ⟪ c ⟫    ⟧ ρ = return (inC⟦ c ⟧ ρ)
inV⟦ ⟦ c ⟧    ⟧ ρ = inC⟦ c ⟧ ρ
inV⟦ con x Ds ⟧ ρ = return (el x) <*> inDs⟦ Ds ⟧ ρ

inDs⟦ ⟨⟩     ⟧ ρ = return ⟨⟩
inDs⟦ Ds ◃ v ⟧ ρ = return _◃_ <*> inDs⟦ Ds ⟧ ρ <*> inV⟦ v ⟧ ρ

exC⟦_⟧ : forall {M Γ C} -> ExC M Γ C -> Env Γ -> Monad M CTy⟦ C ⟧

inC⟦ ƛ c     ⟧ ρ = \v -> inC⟦ c ⟧ (ρ ◃ v)
inC⟦ exC c m ⟧ ρ = morph m _ =<< exC⟦ c ⟧ ρ
inC⟦ inV v   ⟧ ρ = inV⟦ v ⟧ ρ

exC⟦ var x ⟧ ρ = return (return (ρ ! x))
exC⟦ f • s ⟧ ρ = exC⟦ f ⟧ ρ <*> inV⟦ s ⟧ ρ
