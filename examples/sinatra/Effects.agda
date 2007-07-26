
open import Prelude

module Effects
  (Name   : Set)

  -- Data stuff
  (Datatype : Name -> List (List Name))

  -- Effect stuff
  (Effect : Set)
  (Id     : Effect)
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

mutual
  data CTy : Set where
    _⟶_  : VTy -> CTy -> CTy
    [_]_ : Effect -> VTy -> CTy

  data VTy : Set where
    ⟨_⟩   : CTy -> VTy
    TyCon : Name -> VTy

mutual
  data InC : Set where
    λ_,_ : Name -> InC -> InC
    exC  : ExC -> InC
    inV  : InV -> InC

  data ExC : Set where
    var : Name -> ExC
    _•_ : ExC -> InV -> ExC

  data InV : Set where
    ⟪_⟫ : InC -> InV
    ⟦_⟧ : InC -> InV
    con : forall {D args} -> args ∈ Datatype D -> List InV -> InV

Cxt = List (Name × VTy)

infix 10 _⊢_∋_ <_>_⊢_∋_ <_>_⊢_∈_

mutual
  data _⊢_∋_ : Cxt -> CTy -> InC -> Set where

    checkλ : forall {V C Γ x t} ->
          Γ ◄ x , V ⊢ C ∋ t
       -> -------------------
          Γ ⊢ V ⟶ C ∋ λ x , t

    checkExC : forall {M N Γ V c} ->
          < M > Γ ⊢ c ∈ [ N ] V  ->  N ⊆ M
      ->  --------------------------------
                 Γ ⊢ [ M ] V ∋ exC c

    checkInV : forall {M Γ V v} ->
            < M > Γ ⊢ V ∋ v
      ->  -------------------
          Γ ⊢ [ M ] V ∋ inV v
    

  data <_>_⊢_∋_ : Effect -> Cxt -> VTy -> InV -> Set where

    check⟪_⟫ : forall {M Γ C c} ->
                 Γ ⊢ C ∋ c
      ->  -----------------------
          < M > Γ ⊢ ⟨ C ⟩ ∋ ⟪ c ⟫

    check⟦_⟧ : forall {M Γ V c} ->
            Γ ⊢ [ M ] V ∋ c
      ->  -------------------
          < M > Γ ⊢ V ∋ ⟦ c ⟧

    checkCon : forall {M Γ D vs args x} ->
                  < M > Γ ⊢ args ∋s vs
      ->  --------------------------------------
          < M > Γ ⊢ TyCon D ∋ con {D}{args} x vs

  data <_>_⊢_∋s_ : Effect -> Cxt -> List Name -> List InV -> Set where

    checkε : forall {M Γ} ->
          < M > Γ ⊢ ε ∋s ε

    check◄ : forall {M Γ D Ds v vs} ->
          < M > Γ ⊢ Ds ∋s vs  ->  < M > Γ ⊢ TyCon D ∋ v
      ->  ---------------------------------------------
                  < M > Γ ⊢ Ds ◄ D ∋s vs ◄ v

  data <_>_⊢_∈_ : Effect -> Cxt -> ExC -> CTy -> Set where

    inferVar : forall {M Γ x V} ->
                  x , V ∈ Γ
      ->  --------------------------
          < M > Γ ⊢ var x ∈ [ M ] V

    inferApp : forall {M Γ V C f s} ->

          < M > Γ ⊢ f ∈ V ⟶ C  ->  < M > Γ ⊢ V ∋ s
      ->  ----------------------------------------
                   < M > Γ ⊢ f • s ∈ C

mutual
  data El : Name -> Set where
    el : forall {args D} -> args ∈ Datatype D -> Els args -> El D

  data Els : List Name -> Set where
    ⟨⟩  : Els ε
    _◃_ : forall {D Ds} -> Els Ds -> El D -> Els (Ds ◄ D)

mutual
  CTy⟦_⟧ : CTy -> Set
  CTy⟦ V ⟶ C   ⟧ = VTy⟦ V ⟧ -> CTy⟦ C ⟧
  CTy⟦ [ M ] V ⟧ = Monad M VTy⟦ V ⟧
  
  VTy⟦_⟧ : VTy -> Set
  VTy⟦ ⟨ C ⟩   ⟧ = CTy⟦ C ⟧
  VTy⟦ TyCon D ⟧ = El D

data Env : Cxt -> Set where
  •    : Env ε
  _::_ : forall {Γ V x} -> Env Γ -> VTy⟦ V ⟧ -> Env (Γ ◄ x , V)

_!_ : forall {Γ x V} -> Env Γ -> x , V ∈ Γ -> VTy⟦ V ⟧
(_ :: v) ! hd   = v
(ρ :: _) ! tl x = ρ ! x

mutual
  inV⟦_⟧ : forall {M Γ V v} -> < M > Γ ⊢ V ∋ v -> Env Γ -> Monad M VTy⟦ V ⟧
  inV⟦ check⟪ c ⟫          ⟧ ρ = return (inC⟦ c ⟧ ρ)
  inV⟦ check⟦ c ⟧          ⟧ ρ = inC⟦ c ⟧ ρ
  inV⟦ checkCon {x = x} Ds ⟧ ρ = return (el x) <*> inDs⟦ Ds ⟧ ρ

  inDs⟦_⟧ : forall {M Γ Ds vs} ->
            < M > Γ ⊢ Ds ∋s vs -> Env Γ -> Monad M (Els Ds)
  inDs⟦ checkε      ⟧ ρ = return ⟨⟩
  inDs⟦ check◄ Ds v ⟧ ρ = return _◃_ <*> inDs⟦ Ds ⟧ ρ <*> inV⟦ v ⟧ ρ 

  inC⟦_⟧ : forall {Γ C c} -> Γ ⊢ C ∋ c -> Env Γ -> CTy⟦ C ⟧
  inC⟦ checkλ c     ⟧ ρ = \v -> inC⟦ c ⟧ (ρ :: v)
  inC⟦ checkExC c m ⟧ ρ = morph m _ =<< exC⟦ c ⟧ ρ
  inC⟦ checkInV v   ⟧ ρ = inV⟦ v ⟧ ρ

  exC⟦_⟧ : forall {M Γ C c} -> < M > Γ ⊢ c ∈ C -> Env Γ -> Monad M CTy⟦ C ⟧
  exC⟦ inferVar x   ⟧ ρ = return (return (ρ ! x))
  exC⟦ inferApp f s ⟧ ρ = exC⟦ f ⟧ ρ <*> inV⟦ s ⟧ ρ
