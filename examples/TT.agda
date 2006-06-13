
module TT where

module Prelude where

-- Props ------------------------------------------------------------------

  data True : Prop where
    tt : True

  data False : Prop where

  postulate
    falseE : (A:Set) -> False -> A

  infix 3 /\

  data (/\)(P,Q:Prop) : Prop where
    andI : P -> Q -> P /\ Q

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

  module NatEq where

    infix 5 ==

    (==) : Nat -> Nat -> Prop
    zero  == zero = True
    suc n == suc m = n == m
    _	  == _	   = False

    rewrite : (C:Nat -> Set) -> {m,n:Nat} -> m == n -> C n -> C m
    rewrite C {zero}  {zero}  _	 x = x
    rewrite C {suc _} {suc _} eq x = rewrite (\z -> C (suc z)) eq x

module Chain {A:Set}((==) : A -> A -> Prop)
	     (trans : {x,y,z:A} -> x == y -> y == z -> x == z)
    where

  infixl 4 =-=, ===
  infixr 8 `since`

  (=-=) : (x:A) -> {y:A} -> x == y -> x == y
  x =-= xy = xy

  (===) : {x,y,z:A} -> x == y -> y == z -> x == z
  xy === yz = trans xy yz

  since : {x:A} -> (y:A) -> x == y -> x == y
  since y xy = xy

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

  module FinEq where

    infix 5 ==

    (==) : {n:Nat} -> Fin n -> Fin n -> Prop
    (==) {suc _} (finI  fzero_	) (finI  fzero_	 ) = True
    (==) {suc _} (finI (fsuc_ i)) (finI (fsuc_ j)) = i == j
    (==)	  _		   _		   = False

    rewrite : {n:Nat} -> (C:Fin n -> Set) -> {i,j:Fin n} -> i == j -> C j -> C i
    rewrite {suc _} C {finI  fzero_  } {finI  fzero_  } eq x = x
    rewrite {suc _} C {finI (fsuc_ i)} {finI (fsuc_ j)} eq x = rewrite (\z -> C (fsuc z)) eq x

module Vec where

  open Prelude
  open Fin

  infixr 15 ::

  -- Vectors ----------------------------------------------------------------

  data Nil : Set where
    nil_ : Nil

  data Cons (A,As:Set) : Set where
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

  map : {n:Nat} -> {A,B:Set} -> (A -> B) -> Vec A n -> Vec B n
  map {zero}  f (vecI nil_)	    = nil
  map {suc n} f (vecI (cons_ x xs)) = f x :: map f xs

  (!) : {n:Nat} -> {A:Set} -> Vec A n -> Fin n -> A
  (!) {suc n} (vecI (cons_ x _ )) (finI fzero_)    = x
  (!) {suc n} (vecI (cons_ _ xs)) (finI (fsuc_ i)) = xs ! i

  tabulate : {n:Nat} -> {A:Set} -> (Fin n -> A) -> Vec A n
  tabulate {zero}  f = nil
  tabulate {suc n} f = f fzero :: tabulate (\x -> f (fsuc x))

module Untyped where

  open Prelude
  open Fin
  open Vec

  Name = Nat

  data Expr (n:Nat) : Set where
    eVar : Fin n -> Expr n
    eApp : Expr n -> Expr n -> Expr n
    eLam : Expr (suc n) -> Expr n
    eSet : Expr n
    eEl  : Expr n
    ePi  : Expr n
    eCon : Name -> Expr n

  module ExprEq where

    infix 5 ==

    (==) : {n:Nat} -> Expr n -> Expr n -> Prop
    eVar i	        == eVar j		 = FinEq.== i j
    eApp e1 e2		== eApp e3 e4		 = e1 == e3 /\ e2 == e4
    eLam e1		== eLam e2		 = e1 == e2
    eSet		== eSet			 = True
    eEl		        == eEl			 = True
    ePi			== ePi			 = True
    eCon f		== eCon g		 = NatEq.== f g
    _			== _			 = False

    rewrite : {n:Nat} -> (C:Expr n -> Set) -> {r,s:Expr n} -> r == s -> C s -> C r
    rewrite {_} C {eVar i    } {eVar j	  } eq x = FinEq.rewrite (\z -> C (eVar z)) eq x
    rewrite {_} C {eLam e1   } {eLam e2	  } eq x = rewrite (\z -> C (eLam z)) eq x
    rewrite {_} C {eSet	     } {eSet	  } eq x = x
    rewrite {_} C {eEl	     } {eEl	  } eq x = x
    rewrite {_} C {ePi	     } {ePi	  } eq x = x
    rewrite {_} C {eCon f    } {eCon g	  } eq x = NatEq.rewrite (\z -> C (eCon z)) eq x
    rewrite {_} C {eApp e1 e2} {eApp e3 e4} (andI eq13 eq24) x =
      rewrite (\z -> C (eApp z e2)) eq13 (
	rewrite (\z -> C (eApp e3 z)) eq24 x
      )

module Typed where

  open Prelude
  open Fin
  open Vec

  mutual

    infixl 15 &
    infix  13 !!
    infix  5  ==

    -- Contexts ---------------------------------------------------------------

    Context_ : Nat -> Set
    Context_ zero    = Nil
    Context_ (suc n) = CSuc n

    data CSuc (n:Nat) : Set where
      ext : (Γ : Context n) -> Type Γ -> Context_ (suc n)

    data Context (n:Nat) : Set where
      ctxI : Context_ n -> Context n

    -- Types ------------------------------------------------------------------

    data Type {n:Nat}(Γ:Context n) : Set where
      SET : Type Γ
      Pi  : (A:Type Γ) -> Type (Γ & A) -> Type Γ
      El  : Term Γ SET -> Type Γ

    (&) : {n:Nat} -> (Γ:Context n) -> Type Γ -> Context (suc n)
    Γ & A = ctxI (ext Γ A)

    -- Variables --------------------------------------------------------------

    Var_ : {n:Nat} -> (Γ:Context n) -> Type Γ -> Set
    Var_ {zero}	  Γ		  A = Zero
    Var_ {suc n} (ctxI (ext Γ B)) A = VarSuc Γ B A

    data VarSuc {n:Nat}(Γ:Context n)(B:Type Γ)(A:Type (Γ & B)) : Set where
      vzero_ : A == rename upR B -> Var_ (Γ & B) A
      vsuc_  : (C:Type Γ) -> A == rename upR C -> Var Γ C -> Var_ (Γ & B) A

    data Var {n:Nat}(Γ:Context n)(A:Type Γ) : Set where
      varI : Var_ Γ A -> Var Γ A

    -- Terms ------------------------------------------------------------------

    data Term {n:Nat}(Γ:Context n)(A:Type Γ) : Set where
      var : (x:Var Γ A) -> Term Γ A
      app : {B:Type Γ} -> {C:Type (Γ & B)} -> Term Γ (Pi B C) -> (t:Term Γ B) ->
	    A == subst (down t) C -> Term Γ A
      lam : {B:Type Γ} -> {C:Type (Γ & B)} -> Term (Γ & B) C -> A == Pi B C -> Term Γ A

    -- Context manipulation ---------------------------------------------------

    ∅ : Context zero
    ∅ = ctxI nil_

    (!!) : {n:Nat} -> (Γ:Context n) -> Fin n -> Type Γ
    (!!) {suc _} (ctxI (ext Γ A)) (finI fzero_)	   = rename upR A
    (!!) {suc _} (ctxI (ext Γ A)) (finI (fsuc_ i)) = rename upR (Γ !! i)

    -- Renamings --------------------------------------------------------------

    Ren_ : {n,m:Nat} -> Context n -> Context m -> Set
    Ren_ {zero}  {m} (ctxI nil_)      Δ = Nil
    Ren_ {suc n} {m} (ctxI (ext Γ A)) Δ = ConsRen Γ A Δ

    data ConsRen {n,m:Nat}(Γ:Context n)(A:Type Γ)(Δ:Context m) : Set where
      extRen_ : (ρ : Ren Γ Δ) -> Var Δ (rename ρ A) -> Ren_ (Γ & A) Δ

    data Ren {n,m:Nat}(Γ:Context n)(Δ:Context m) : Set where
      renI : Ren_ Γ Δ -> Ren Γ Δ

    -- Performing renamings ---------------------------------------------------

    rename : {n,m:Nat} -> {Γ:Context n} -> {Δ:Context m} -> Ren Γ Δ -> Type Γ -> Type Δ
    rename ρ SET = SET
    rename ρ A	 = rename' ρ A

    rename' : {n,m:Nat} -> {Γ:Context n} -> {Δ:Context m} -> Ren Γ Δ -> Type Γ -> Type Δ
    rename' ρ SET      = SET
    rename' ρ (Pi A B) = Pi (rename ρ A) (rename (liftR ρ) B)
    rename' ρ (El t)   = El (renameTerm ρ t)

    renameTerm : {n,m:Nat} -> {Γ:Context n} -> {Δ:Context m} -> {A:Type Γ} ->
		 (ρ:Ren Γ Δ) -> Term Γ A -> Term Δ (rename ρ A)
    renameTerm ρ (var x)      = var (lookupR ρ x)
    renameTerm {_}{_}{_}{_}{A} ρ (app{_}{C} s t eq) =
	app (renameTerm ρ s) (renameTerm ρ t)
	    (cong (rename ρ) eq `trans` renameSubstCommute)
    renameTerm ρ (lam t eq)   = lam (renameTerm (liftR ρ) t) (cong (rename ρ) eq)

    lookupR : {n,m:Nat} -> {Γ:Context n} -> {A:Type Γ} -> {Δ:Context m} ->
	      (ρ:Ren Γ Δ) -> (x:Var Γ A) -> Var Δ (rename ρ A)
    lookupR {suc n} {_} {ctxI (ext _ _)}
	    (renI (extRen_ ρ t)) _    = ?

    -- Building renamings -----------------------------------------------------

    extRen : {n,m:Nat} -> {Γ:Context n} -> {A:Type Γ} -> {Δ:Context m} ->
	     (ρ : Ren Γ Δ) -> Var Δ (rename ρ A) -> Ren (Γ & A) Δ
    extRen ρ x = renI (extRen_ ρ x)

    liftR : {n,m:Nat} -> {Γ:Context n} -> {A:Type Γ} -> {Δ:Context m} ->
	    (ρ:Ren Γ Δ) -> Ren (Γ & A) (Δ & rename ρ A)
    liftR {_}{_}{_}{A} ρ = extRen (coR upR ρ) (varI ?)

    idR : {n:Nat} ->  {Γ:Context n} -> Ren Γ Γ
    idR = ?

    coR : {n,m,p:Nat} -> {Γ:Context n} -> {Δ:Context m} -> {Θ:Context p} -> Ren Δ Θ -> Ren Γ Δ -> Ren Γ Θ
    coR = ?

    upR : {n:Nat} -> {Γ:Context n} -> {A:Type Γ} -> Ren Γ (Γ & A)
    upR = ?

    -- Substitutions ----------------------------------------------------------

    Sub_ : {n,m:Nat} -> Context n -> Context m -> Set
    Sub_ {zero}  {m} (ctxI nil_)      Δ = Nil
    Sub_ {suc n} {m} (ctxI (ext Γ A)) Δ = ConsSub Γ A Δ

    data ConsSub {n,m:Nat}(Γ:Context n)(A:Type Γ)(Δ:Context m) : Set where
      extSub_ : (σ : Sub Γ Δ) -> Term Δ (subst σ A) -> Sub_ (Γ & A) Δ

    data Sub {n,m:Nat}(Γ:Context n)(Δ:Context m) : Set where
      subI : Sub_ Γ Δ -> Sub Γ Δ

    -- Performing substitution ------------------------------------------------

    subst : {n,m:Nat} -> {Γ:Context n} -> {Δ:Context m} -> Sub Γ Δ -> Type Γ -> Type Δ
    subst σ SET	      = SET
    subst σ A	      = subst' σ A

    subst' : {n,m:Nat} -> {Γ:Context n} -> {Δ:Context m} -> Sub Γ Δ -> Type Γ -> Type Δ
    subst' σ (Pi A B) = Pi (subst σ A) (subst (liftS σ) B)
    subst' σ (El t)   = El (substTerm σ t)
    subst' σ SET      = SET

    substTerm : {n,m:Nat} -> {Γ:Context n} -> {Δ:Context m} -> {A:Type Γ} ->
		(σ:Sub Γ Δ) -> Term Γ A -> Term Δ (subst σ A)
    substTerm σ (var x)	     = ?
    substTerm σ (app s t eq) = ?
    substTerm σ (lam t eq)   = ?

    -- Building substitutions -------------------------------------------------

    liftS : {n,m:Nat} -> {Γ:Context n} -> {A:Type Γ} -> {Δ:Context m} ->
	    (σ:Sub Γ Δ) -> Sub (Γ & A) (Δ & subst σ A)
    liftS {_}{_}{_}{A} σ = ? -- extSub (upS ∘ σ) (var fzero (substCompose upS σ A))
      -- Works with hidden args to substCompose when inlined in subst,
      -- but not here. Weird.

    topS : {n:Nat} -> {Γ:Context n} -> Sub ∅ Γ
    topS = subI nil_

    extSub : {n,m:Nat} -> {Γ:Context n} -> {A:Type Γ} -> {Δ:Context m} ->
	     (σ : Sub Γ Δ) -> Term Δ (subst σ A) -> Sub (Γ & A) Δ
    extSub σ t = subI (extSub_ σ t)

    idS : {n:Nat} -> {Γ:Context n} -> Sub Γ Γ
    idS {zero}  {ctxI nil_}	 = topS
    idS {suc _} {ctxI (ext Γ A)} = ? -- extSub upS (var fzero refl)

    (∘) : {n,m,p:Nat} -> {Γ:Context n} -> {Δ:Context m} -> {Θ:Context p} -> Sub Δ Θ -> Sub Γ Δ -> Sub Γ Θ
    (∘) {zero} {_}{_} {ctxI nil_}      _  _		      = topS
    (∘) {suc _}{_}{_} {ctxI (ext Γ A)} σ (subI (extSub_ δ t)) =
      extSub (σ ∘ δ) (convert (substCompose σ δ A) (substTerm σ t))

    upS : {n:Nat} -> {Γ:Context n} -> {A:Type Γ} -> Sub Γ (Γ & A)
    upS = ?

    down : {n:Nat} -> {Γ:Context n} -> {A:Type Γ} -> Term Γ A -> Sub (Γ & A) Γ
    down t = extSub idS (convert substId t)

    -- Convertibility ---------------------------------------------------------

    (==) : {n:Nat} -> {Γ:Context n} -> Type Γ -> Type Γ -> Prop
    A == B = ?

    refl : {n:Nat} -> {Γ:Context n} -> {A:Type Γ} -> A == A
    refl = ?

    cong : {n,m:Nat} -> {Γ:Context n} -> {Δ:Context m} -> (f:Type Γ -> Type Δ) ->
	   {A,B:Type Γ} -> A == B -> f A == f B
    cong f eq = ?

    trans : {n:Nat} -> {Γ:Context n} -> {A,B,C:Type Γ} -> A == B -> B == C -> A == C
    trans ab bc = ?

    convert : {n:Nat} -> {Γ:Context n} -> {A,B:Type Γ} -> A == B -> Term Γ B -> Term Γ A
    convert eq t = ?

    -- Properties -------------------------------------------------------------

    renameId : {n:Nat} -> {Γ:Context n} -> {A:Type Γ} -> rename idR A == A
    renameId = ?

    renameCompose : {n,m,p:Nat} -> {Γ:Context n} -> {Δ:Context m} -> {Θ:Context p} ->
		    (σ:Ren Δ Θ) -> (δ:Ren Γ Δ) -> (A:Type Γ) -> 
		    rename (σ `coR` δ) A == rename σ (rename δ A)
    renameCompose σ δ A = ?

    substId : {n:Nat} -> {Γ:Context n} -> {A:Type Γ} -> subst idS A == A
    substId = ?

    substCompose : {n,m,p:Nat} -> {Γ:Context n} -> {Δ:Context m} -> {Θ:Context p} ->
		   (σ:Sub Δ Θ) -> (δ:Sub Γ Δ) -> (A:Type Γ) -> 
		   subst (σ ∘ δ) A == subst σ (subst δ A)
    substCompose σ δ A = ?

    renameSubstCommute :
      {n,m:Nat} -> {Γ:Context n} -> {Δ:Context m} -> {A:Type Γ} -> {B:Type (Γ & A)} ->
      {ρ:Ren Γ Δ} -> {t:Term Γ A} ->
      rename ρ (subst (down t) B) == subst (down (renameTerm ρ t)) (rename (liftR ρ) B)
    renameSubstCommute = ?

