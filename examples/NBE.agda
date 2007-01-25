
-- NBE for Gödel System T
module NBE where

module Prelude where

  -- Zero and One -----------------------------------------------------------

  data Zero : Set where

  data One : Set where
    unit : One

  -- Natural numbers --------------------------------------------------------

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

  (+) : Nat -> Nat -> Nat
  zero  + m = m
  suc n + m = suc (n + m)

-- Props ------------------------------------------------------------------

  data True : Prop where
    tt : True

  data False : Prop where

  postulate
    falseE : (A:Set) -> False -> A

  infix 3 /\

  data (/\)(P Q:Prop) : Prop where
    andI : P -> Q -> P /\ Q

module Fin where

  open Prelude

  -- Finite sets ------------------------------------------------------------

  data Suc (A:Set) : Set where
    fzero_ : Suc A
    fsuc_  : A -> Suc A

  mutual

    data Fin (n:Nat) : Set where
      finI : Fin_ n -> Fin n

    Fin_ : Nat -> Set
    Fin_  zero   = Zero
    Fin_ (suc n) = Suc (Fin n)

  fzero : {n:Nat} -> Fin (suc n)
  fzero = finI fzero_

  fsuc : {n:Nat} -> Fin n -> Fin (suc n)
  fsuc i = finI (fsuc_ i)

  finE : {n:Nat} -> Fin n -> Fin_ n
  finE (finI i) = i

module Vec where

  open Prelude
  open Fin

  infixr 15 ::

  -- Vectors ----------------------------------------------------------------

  data Nil : Set where
    nil_ : Nil

  data Cons (A As:Set) : Set where
    cons_ : A -> As -> Cons A As

  mutual

    data Vec (A:Set)(n:Nat) : Set where
      vecI : Vec_ A n -> Vec A n

    Vec_ : Set -> Nat -> Set
    Vec_ A  zero   = Nil
    Vec_ A (suc n) = Cons A (Vec A n)

  nil : {A:Set} -> Vec A zero
  nil = vecI nil_

  (::) : {A:Set} -> {n:Nat} -> A -> Vec A n -> Vec A (suc n)
  x :: xs = vecI (cons_ x xs)

  vecE : {A:Set} -> {n:Nat} -> Vec A n -> Vec_ A n
  vecE (vecI xs) = xs

  vec : {A:Set} -> (n:Nat) -> A -> Vec A n
  vec  zero   _ = nil
  vec (suc n) x = x :: vec n x

  map : {n:Nat} -> {A B:Set} -> (A -> B) -> Vec A n -> Vec B n
  map {zero}  f (vecI nil_)	    = nil
  map {suc n} f (vecI (cons_ x xs)) = f x :: map f xs

  (!) : {n:Nat} -> {A:Set} -> Vec A n -> Fin n -> A
  (!) {suc n} (vecI (cons_ x _ )) (finI fzero_)    = x
  (!) {suc n} (vecI (cons_ _ xs)) (finI (fsuc_ i)) = xs ! i

  tabulate : {n:Nat} -> {A:Set} -> (Fin n -> A) -> Vec A n
  tabulate {zero}  f = nil
  tabulate {suc n} f = f fzero :: tabulate (\x -> f (fsuc x))

module Syntax where

  open Prelude
  open Fin

  -- Types ------------------------------------------------------------------

  infixr 8 =>

  data Type : Set where
    nat  : Type
    (=>) : Type -> Type -> Type

  -- Terms ------------------------------------------------------------------

  data Term (n:Nat) : Set where
    eZero : Term n
    eSuc  : Term n
    eApp  : Term n -> Term n -> Term n
    eLam  : Term (suc n) -> Term n
    eVar  : Fin n -> Term n

module NormalForms where

  open Prelude
  open Syntax
  open Fin

  mutual

    -- Normal terms -----------------------------------------------------------

    data Normal (n:Nat) : Set where
      nZero    : Normal n
      nSuc     : Normal n -> Normal n
      nLam     : Normal (suc n) -> Normal n
      nNeutral : Neutral n -> Normal n
      nStuck   : Normal n		-- type error

    -- Neutral terms ----------------------------------------------------------

    data Neutral (n:Nat) : Set where
      uVar : Fin n -> Neutral n
      uApp : Neutral n -> Normal n -> Neutral n

  nVar : {n:Nat} -> Fin n -> Normal n
  nVar i = nNeutral (uVar i)

  nApp : {n:Nat} -> Neutral n -> Normal n -> Normal n
  nApp u n = nNeutral (uApp u n)

module Rename where

  open Prelude
  open Fin
  open Vec
  open NormalForms

  -- Renamings --------------------------------------------------------------

  Ren : Nat -> Nat -> Set
  Ren m n = Vec (Fin n) m

  id : {n:Nat} -> Ren n n
  id = tabulate (\i -> i)

  compose : {l m n:Nat} -> Ren m n -> Ren l m -> Ren l n
  compose {l}{m}{n} ρ γ = map (\i -> ρ ! i) γ

  lift : {m n:Nat} -> Ren m n -> Ren (suc m) (suc n)
  lift ρ = fzero :: map fsuc ρ

  mutual

    rename : {m n:Nat} -> Ren m n -> Normal m -> Normal n
    rename ρ nZero	  = nZero
    rename ρ (nSuc n)	  = nSuc (rename ρ n)
    rename ρ (nLam n)	  = nLam (rename (lift ρ) n)
    rename ρ (nNeutral u) = nNeutral (renameNe ρ u)
    rename ρ  nStuck	  = nStuck

    renameNe : {m n:Nat} -> Ren m n -> Neutral m -> Neutral n
    renameNe ρ (uVar i)	  = uVar (ρ ! i)
    renameNe ρ (uApp u n) = uApp (renameNe ρ u) (rename ρ n)

  up : {n:Nat} -> Ren n (suc n)
  up = map fsuc id

module Subst where

  open Prelude
  open Fin
  open Vec
  open NormalForms
  open Rename using (Ren; rename; up)

  -- Substitutions ----------------------------------------------------------

  Sub : Nat -> Nat -> Set
  Sub m n = Vec (Normal n) m

  id : {n:Nat} -> Sub n n
  id = tabulate nVar

  ren2sub : {m n:Nat} -> Ren m n -> Sub m n
  ren2sub ρ = map nVar ρ

  lift : {m n:Nat} -> Sub m n -> Sub (suc m) (suc n)
  lift σ = nVar fzero :: map (rename up) σ

  mutual

    app : {n:Nat} -> Normal n -> Normal n -> Normal n
    app  nZero	     _ = nStuck
    app (nSuc _)     _ = nStuck
    app  nStuck	     _ = nStuck
    app (nLam u)     v = subst (v :: id) u
    app (nNeutral n) v = nApp n v

    subst : {m n:Nat} -> Sub m n -> Normal m -> Normal n
    subst σ  nZero	 = nZero
    subst σ (nSuc v)	 = nSuc (subst σ v)
    subst σ (nLam v)	 = nLam (subst (lift σ) v)
    subst σ (nNeutral n) = substNe σ n
    subst σ  nStuck	 = nStuck

    substNe : {m n:Nat} -> Sub m n -> Neutral m -> Normal n
    substNe σ (uVar i)	 = σ ! i
    substNe σ (uApp n v) = substNe σ n `app` subst σ v

  compose : {l m n:Nat} -> Sub m n -> Sub l m -> Sub l n
  compose σ δ = map (subst σ) δ

module TypeSystem where

  open Prelude
  open Fin
  open Vec
  open Syntax

  mutual
    EqType : Type -> Type -> Prop
    EqType  nat	    nat	       = True
    EqType (τ => τ') (σ => σ') = τ == σ /\ τ' == σ'
    EqType  _	    _	       = False

    infix 5 ==
    data (==) (τ0 τ1:Type) : Prop where
      eqTypeI : EqType τ0 τ1 -> τ0 == τ1

  eqSubst : {σ τ:Type} -> (C:Type -> Set) -> σ == τ -> C τ -> C σ
  eqSubst {nat}{nat} C _ x = x
  eqSubst {σ => τ}{σ' => τ'} C (eqTypeI (andI eqσ eqτ)) x =
    eqSubst (\μ -> C (μ => τ)) eqσ (
      eqSubst (\η -> C (σ' => η)) eqτ x
    )

  Context : Nat -> Set
  Context n = Vec Type n

  mutual

    HasType : {n:Nat} -> Context n -> Term n -> Type -> Set
    HasType Γ eZero	   τ = ZeroType Γ τ
    HasType Γ eSuc	   τ = SucType  Γ τ
    HasType Γ (eVar i)	   τ = VarType  Γ i τ
    HasType Γ (eApp e1 e2) τ = AppType  Γ e1 e2 τ
    HasType Γ (eLam e)	   τ = LamType  Γ e τ

    data ZeroType {n:Nat}(Γ:Context n)(τ:Type) : Set where
      zeroType : τ == nat -> HasType Γ eZero τ

    data SucType {n:Nat}(Γ:Context n)(τ:Type) : Set where
      sucType : τ == (nat => nat) -> HasType Γ eSuc τ

    data VarType {n:Nat}(Γ:Context n)(i:Fin n)(τ:Type) : Set where
      varType : τ == (Γ ! i) -> HasType Γ (eVar i) τ

    data AppType {n:Nat}(Γ:Context n)(e1 e2:Term n)(τ:Type) : Set where
      appType : (σ:Type) -> HasType Γ e1 (σ => τ) -> HasType Γ e2 σ -> HasType Γ (eApp e1 e2) τ

    data LamType {n:Nat}(Γ:Context n)(e:Term (suc n))(τ:Type) : Set where
      lamType : (τ0 τ1:Type) -> τ == (τ0 => τ1) -> HasType (τ0 :: Γ) e τ1 -> HasType Γ (eLam e) τ

module NBE where

  open Prelude
  open Syntax
  open Fin
  open Vec
  open TypeSystem

  mutual

    D_ : Nat -> Type -> Set
    D_ n nat      = NatD n
    D_ n (σ => τ) = FunD n σ τ

    data D (n:Nat)(τ:Type) : Set where
      dI : D_ n τ -> D n τ

    data NatD (n:Nat) : Set where
      zeroD_ :		  D_ n nat
      sucD_  : D n nat -> D_ n nat
      neD_   : Term n  -> D_ n nat

    -- Will this pass the positivity check?
    data FunD (n:Nat)(σ τ:Type) : Set where
      lamD_  : (D n σ -> D n τ) -> D_ n (σ => τ)

  zeroD : {n:Nat} -> D n nat
  zeroD = dI zeroD_

  sucD : {n:Nat} -> D n nat -> D n nat
  sucD d = dI (sucD_ d)

  neD : {n:Nat} -> Term n -> D n nat
  neD t = dI (neD_ t)

  lamD : {n:Nat} -> {σ τ:Type} -> (D n σ -> D n τ) -> D n (σ => τ)
  lamD f = dI (lamD_ f)

  coerce : {n:Nat} -> {τ0 τ1:Type} -> τ0 == τ1 -> D n τ1 -> D n τ0
  coerce {n} = eqSubst (D n)

  mutual

    down : {τ:Type} -> {n:Nat} -> D n τ -> Term n
    down {σ => τ} (dI (lamD_ f)) = eLam (down {τ} ?)  -- doesn't work!
    down {nat}	  (dI zeroD_)    = eZero
    down {nat}	  (dI (sucD_ d)) = eSuc `eApp` down d
    down {nat}	  (dI (neD_ t))  = t

    up : {n:Nat} -> (τ:Type) -> Term n -> D n τ
    up (σ => τ) t = lamD (\d -> up τ (t `eApp` down d))
    up  nat	t = neD t

  Valuation : {m:Nat} -> Nat -> Context m -> Set
  Valuation {zero}  n  _		 = Nil
  Valuation {suc m} n (vecI (cons_ τ Γ)) = Cons (D n τ) (Valuation n Γ)

  (!!) : {m n:Nat} -> {Γ:Context m} -> Valuation n Γ -> (i:Fin m) -> D n (Γ ! i)
  (!!) {suc _} {_} {vecI (cons_ _ _)} (cons_ v ξ) (finI fzero_) = v
  (!!) {suc _} {_} {vecI (cons_ _ _)} (cons_ v ξ) (finI (fsuc_ i)) = ξ !! i

  ext : {m n:Nat} -> {τ:Type} -> {Γ:Context m} -> Valuation n Γ -> D n τ -> Valuation n (τ :: Γ)
  ext ξ v = cons_ v ξ

  app : {σ τ:Type} -> {n:Nat} -> D n (σ => τ) -> D n σ -> D n τ
  --app (dI (lamD_ f)) d = f d
  app (lamD f) d = f d

  eval : {n:Nat} -> {Γ:Context n} -> (e:Term n) -> (τ:Type) -> HasType Γ e τ -> Valuation n Γ -> D n τ
  eval (eVar i)   τ (varType eq)	  ξ = coerce eq (ξ !! i)
  eval (eApp r s) τ (appType σ dr ds)	  ξ = eval r (σ => τ) dr ξ `app` eval s σ ds ξ
  eval (eLam r)	  τ (lamType τ0 τ1 eq dr) ξ = coerce eq (lamD (\d -> ?))  -- doesn't work either
  eval  eZero	  τ (zeroType eq)	  ξ = coerce eq zeroD
  eval  eSuc	  τ (sucType eq)	  ξ = coerce eq (lamD sucD)

module Eval where

  open Prelude
  open Fin
  open Vec
  open Syntax
  open NormalForms
  open Rename using (up; rename)
  open Subst
  open TypeSystem

  eval : {n:Nat} -> (Γ:Context n) -> (e:Term n) -> (τ:Type) -> HasType Γ e τ -> Normal n
  eval Γ eZero	      τ  _		    = nZero
  eval Γ eSuc	      τ  _		    = nLam (nSuc (nVar fzero))
  eval Γ (eVar i)     τ  _		    = nVar i
  eval Γ (eApp e1 e2) τ (appType σ d1 d2)   = eval Γ e1 (σ => τ) d1 `app` eval Γ e2 σ d2
  eval Γ (eLam e)     τ (lamType τ0 τ1 _ d) = nLam (eval (τ0 :: Γ) e τ1 d)

open Prelude
open Fin
open Vec
open Syntax

