{-# OPTIONS --allow-unsolved-metas --dont-termination-check #-}

module TT where

module Prelude where

-- Props ------------------------------------------------------------------

  data True : Prop where
    tt : True

  data False : Prop where

  postulate
    falseE : (A : Set) -> False -> A

  infix 3 _/\_

  data _/\_ (P Q : Prop) : Prop where
    andI : P -> Q -> P /\ Q

  -- Zero and One -----------------------------------------------------------

  data Zero : Set where

  data One : Set where
    unit : One

  -- Natural numbers --------------------------------------------------------

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

  _+_ : Nat -> Nat -> Nat
  zero  + m = m
  suc n + m = suc (n + m)

  module NatEq where

    infix 5 _==_

    _==_ : Nat -> Nat -> Prop
    zero  == zero = True
    suc n == suc m = n == m
    _	  == _	   = False

    rewrite : (C : Nat -> Set){m n : Nat} -> m == n -> C n -> C m
    rewrite C {zero}  {zero}  _	 x = x
    rewrite C {suc _} {suc _} eq x = rewrite (\z -> C (suc z)) eq x

module Chain {A : Set}(_==_ : A -> A -> Prop)
	     (_trans_ : {x y z : A} -> x == y -> y == z -> x == z)
    where

  infixl 4 _=-=_
  infixl 4 _===_
  infixr 8 _since_

  _=-=_ : (x : A){y : A} -> x == y -> x == y
  x =-= xy = xy

  _===_ : {x y z : A} -> x == y -> y == z -> x == z
  xy === yz = xy trans yz

  _since_ : {x : A}(y : A) -> x == y -> x == y
  y since xy = xy

module Fin where

  open Prelude

  -- Finite sets ------------------------------------------------------------

  data Suc (A : Set) : Set where
    fzero' : Suc A
    fsuc'  : A -> Suc A

  mutual

    data Fin (n : Nat) : Set where
      finI : Fin' n -> Fin n

    Fin' : Nat -> Set
    Fin'  zero   = Zero
    Fin' (suc n) = Suc (Fin n)

  fzero : {n : Nat} -> Fin (suc n)
  fzero = finI fzero'

  fsuc : {n : Nat} -> Fin n -> Fin (suc n)
  fsuc i = finI (fsuc' i)

  finE : {n : Nat} -> Fin n -> Fin' n
  finE (finI i) = i

  module FinEq where

    infix 5 _==_

    _==_ : {n : Nat} -> Fin n -> Fin n -> Prop
    _==_ {suc _} (finI  fzero'	) (finI  fzero'	 ) = True
    _==_ {suc _} (finI (fsuc' i)) (finI (fsuc' j)) = i == j
    _==_	  _		   _		   = False

    rewrite : {n : Nat}(C : Fin n -> Set){i j : Fin n} -> i == j -> C j -> C i
    rewrite {suc _} C {finI  fzero'  } {finI  fzero'  } eq x = x
    rewrite {suc _} C {finI (fsuc' i)} {finI (fsuc' j)} eq x = rewrite (\z -> C (fsuc z)) eq x

module Vec where

  open Prelude
  open Fin

  infixr 15 _::_

  -- Vectors ----------------------------------------------------------------

  data Nil : Set where
    nil' : Nil

  data Cons (A As : Set) : Set where
    cons' : A -> As -> Cons A As

  mutual

    data Vec (A : Set)(n : Nat) : Set where
      vecI : Vec' A n -> Vec A n

    Vec' : Set -> Nat -> Set
    Vec' A  zero   = Nil
    Vec' A (suc n) = Cons A (Vec A n)

  nil : {A : Set} -> Vec A zero
  nil = vecI nil'

  _::_ : {A : Set}{n : Nat} -> A -> Vec A n -> Vec A (suc n)
  x :: xs = vecI (cons' x xs)

  vecE : {A : Set}{n : Nat} -> Vec A n -> Vec' A n
  vecE (vecI xs) = xs

  vec : {A : Set}(n : Nat) -> A -> Vec A n
  vec  zero   _ = nil
  vec (suc n) x = x :: vec n x

  map : {n : Nat}{A B : Set} -> (A -> B) -> Vec A n -> Vec B n
  map {zero}  f (vecI nil')	    = nil
  map {suc n} f (vecI (cons' x xs)) = f x :: map f xs

  _!_ : {n : Nat}{A : Set} -> Vec A n -> Fin n -> A
  _!_ {suc n} (vecI (cons' x _ )) (finI fzero')    = x
  _!_ {suc n} (vecI (cons' _ xs)) (finI (fsuc' i)) = xs ! i

  tabulate : {n : Nat}{A : Set} -> (Fin n -> A) -> Vec A n
  tabulate {zero}  f = nil
  tabulate {suc n} f = f fzero :: tabulate (\x -> f (fsuc x))

module Untyped where

  open Prelude
  open Fin
  open Vec

  Name = Nat

  data Expr (n : Nat) : Set where
    eVar : Fin n -> Expr n
    eApp : Expr n -> Expr n -> Expr n
    eLam : Expr (suc n) -> Expr n
    eSet : Expr n
    eEl  : Expr n
    ePi  : Expr n
    eCon : Name -> Expr n

  module ExprEq where

    infix 5 _==_

    _==_ : {n : Nat} -> Expr n -> Expr n -> Prop
    eVar i	        == eVar j		 = FinEq._==_ i j
    eApp e1 e2		== eApp e3 e4		 = e1 == e3 /\ e2 == e4
    eLam e1		== eLam e2		 = e1 == e2
    eSet		== eSet			 = True
    eEl		        == eEl			 = True
    ePi			== ePi			 = True
    eCon f		== eCon g		 = NatEq._==_ f g
    _			== _			 = False

    rewrite : {n : Nat}(C : Expr n -> Set){r s : Expr n} -> r == s -> C s -> C r
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

    infixl 15 _&_
    infix  13 _!!_
    infix  5  _==_

    -- Contexts ---------------------------------------------------------------

    Context' : Nat -> Set
    Context' zero    = Nil
    Context' (suc n) = CSuc n

    data CSuc (n : Nat) : Set where
      ext : (Γ : Context n) -> Type Γ -> Context' (suc n)

    data Context (n : Nat) : Set where
      ctxI : Context' n -> Context n

    -- Types ------------------------------------------------------------------

    data Type {n : Nat}(Γ : Context n) : Set where
      SET : Type Γ
      Pi  : (A : Type Γ) -> Type (Γ & A) -> Type Γ
      El  : Term Γ SET -> Type Γ

    _&_ : {n : Nat}(Γ : Context n) -> Type Γ -> Context (suc n)
    Γ & A = ctxI (ext Γ A)

    -- Variables --------------------------------------------------------------

    Var' : {n : Nat}(Γ : Context n) -> Type Γ -> Set
    Var' {zero}	  Γ		  A = Zero
    Var' {suc n} (ctxI (ext Γ B)) A = VarSuc Γ B A

    data VarSuc {n : Nat}(Γ : Context n)(B : Type Γ)(A : Type (Γ & B)) : Set where
      vzero_ : A == rename upR B -> Var' (Γ & B) A
      vsuc_  : (C : Type Γ) -> A == rename upR C -> Var Γ C -> Var' (Γ & B) A

    data Var {n : Nat}(Γ : Context n)(A : Type Γ) : Set where
      varI : Var' Γ A -> Var Γ A

    -- Terms ------------------------------------------------------------------

    data Term {n : Nat}(Γ : Context n)(A : Type Γ) : Set where
      var : (x : Var Γ A) -> Term Γ A
      app : {B : Type Γ}{C : Type (Γ & B)} -> Term Γ (Pi B C) -> (t : Term Γ B) ->
	    A == subst (down t) C -> Term Γ A
      lam : {B : Type Γ}{C : Type (Γ & B)} -> Term (Γ & B) C -> A == Pi B C -> Term Γ A

    -- Context manipulation ---------------------------------------------------

    ∅ : Context zero
    ∅ = ctxI nil'

    _!!_ : {n : Nat}(Γ : Context n) -> Fin n -> Type Γ
    _!!_ {suc _} (ctxI (ext Γ A)) (finI fzero')	   = rename upR A
    _!!_ {suc _} (ctxI (ext Γ A)) (finI (fsuc' i)) = rename upR (Γ !! i)

    -- Renamings --------------------------------------------------------------

    Ren' : {n m : Nat} -> Context n -> Context m -> Set
    Ren' {zero}  {m} (ctxI nil')      Δ = Nil
    Ren' {suc n} {m} (ctxI (ext Γ A)) Δ = ConsRen Γ A Δ

    data ConsRen {n m : Nat}(Γ : Context n)(A : Type Γ)(Δ : Context m) : Set where
      extRen' : (ρ : Ren Γ Δ) -> Var Δ (rename ρ A) -> Ren' (Γ & A) Δ

    data Ren {n m : Nat}(Γ : Context n)(Δ : Context m) : Set where
      renI : Ren' Γ Δ -> Ren Γ Δ

    -- Performing renamings ---------------------------------------------------

    rename : {n m : Nat}{Γ : Context n}{Δ : Context m} -> Ren Γ Δ -> Type Γ -> Type Δ
    rename ρ SET = SET
    rename ρ A	 = rename' ρ A

    rename' : {n m : Nat}{Γ : Context n}{Δ : Context m} -> Ren Γ Δ -> Type Γ -> Type Δ
    rename' ρ SET      = SET
    rename' ρ (Pi A B) = Pi (rename ρ A) (rename (liftR ρ) B)
    rename' ρ (El t)   = El (renameTerm ρ t)

    renameTerm : {n m : Nat}{Γ : Context n}{Δ : Context m}{A : Type Γ}
		 (ρ : Ren Γ Δ) -> Term Γ A -> Term Δ (rename ρ A)
    renameTerm ρ (var x)      = var (lookupR ρ x)
    renameTerm {_}{_}{_}{_}{A} ρ (app{_}{C} s t eq) =
	app (renameTerm ρ s) (renameTerm ρ t)
	    (cong (rename ρ) eq  trans  renameSubstCommute)
    renameTerm ρ (lam t eq)   = lam (renameTerm (liftR ρ) t) (cong (rename ρ) eq)

    lookupR : {n m : Nat}{Γ : Context n}{A : Type Γ}{Δ : Context m}
	      (ρ : Ren Γ Δ)(x : Var Γ A) -> Var Δ (rename ρ A)
    lookupR {suc n} {_} {ctxI (ext Γ B)} {A} {Δ}
	    (renI (extRen' ρ z)) (varI (vzero_ eq)) = ?
    lookupR {suc n} {_} {ctxI (ext Γ B)} {A} {Δ}
	    (renI (extRen' ρ z)) (varI (vsuc_ C eq x)) = ?

    -- Building renamings -----------------------------------------------------

    extRen : {n m : Nat}{Γ : Context n}{A : Type Γ}{Δ : Context m}
	     (ρ : Ren Γ Δ) -> Var Δ (rename ρ A) -> Ren (Γ & A) Δ
    extRen ρ x = renI (extRen' ρ x)

    liftR : {n m : Nat}{Γ : Context n}{A : Type Γ}{Δ : Context m} ->
	    (ρ : Ren Γ Δ) -> Ren (Γ & A) (Δ & rename ρ A)
    liftR {_}{_}{_}{A} ρ = extRen (upR coR ρ) (varI ?)

    idR : {n : Nat} {Γ : Context n} -> Ren Γ Γ
    idR = ?

    _coR_ : {n m p : Nat}{Γ : Context n}{Δ : Context m}{Θ : Context p} -> Ren Δ Θ -> Ren Γ Δ -> Ren Γ Θ
    _coR_ = ?

    upR : {n : Nat}{Γ : Context n}{A : Type Γ} -> Ren Γ (Γ & A)
    upR = ?

    -- Substitutions ----------------------------------------------------------

    Sub' : {n m : Nat} -> Context n -> Context m -> Set
    Sub' {zero}  {m} (ctxI nil')      Δ = Nil
    Sub' {suc n} {m} (ctxI (ext Γ A)) Δ = ConsSub Γ A Δ

    data ConsSub {n m : Nat}(Γ : Context n)(A : Type Γ)(Δ : Context m) : Set where
      extSub' : (σ : Sub Γ Δ) -> Term Δ (subst σ A) -> Sub' (Γ & A) Δ

    data Sub {n m : Nat}(Γ : Context n)(Δ : Context m) : Set where
      subI : Sub' Γ Δ -> Sub Γ Δ

    -- Performing substitution ------------------------------------------------

    subst : {n m : Nat}{Γ : Context n}{Δ : Context m} -> Sub Γ Δ -> Type Γ -> Type Δ
    subst σ SET	      = SET
    subst σ A	      = subst' σ A

    subst' : {n m : Nat}{Γ : Context n}{Δ : Context m} -> Sub Γ Δ -> Type Γ -> Type Δ
    subst' σ (Pi A B) = Pi (subst σ A) (subst (liftS σ) B)
    subst' σ (El t)   = El (substTerm σ t)
    subst' σ SET      = SET

    substTerm : {n m : Nat}{Γ : Context n}{Δ : Context m}{A : Type Γ} ->
		(σ : Sub Γ Δ) -> Term Γ A -> Term Δ (subst σ A)
    substTerm σ (var x)	     = ?
    substTerm σ (app s t eq) = ?
    substTerm σ (lam t eq)   = ?

    -- Building substitutions -------------------------------------------------

    liftS : {n m : Nat}{Γ : Context n}{A : Type Γ}{Δ : Context m} ->
	    (σ : Sub Γ Δ) -> Sub (Γ & A) (Δ & subst σ A)
    liftS {_}{_}{_}{A} σ = ? -- extSub (upS ∘ σ) (var fzero (substCompose upS σ A))
      -- Works with hidden args to substCompose when inlined in subst 
      -- but not here. Weird.

    topS : {n : Nat}{Γ : Context n} -> Sub ∅ Γ
    topS = subI nil'

    extSub : {n m : Nat}{Γ : Context n}{A : Type Γ}{Δ : Context m}
	     (σ : Sub Γ Δ) -> Term Δ (subst σ A) -> Sub (Γ & A) Δ
    extSub σ t = subI (extSub' σ t)

    idS : {n : Nat}{Γ : Context n} -> Sub Γ Γ
    idS {zero}  {ctxI nil'}	 = topS
    idS {suc _} {ctxI (ext Γ A)} = ? -- extSub upS (var fzero refl)

    _∘_ : {n m p : Nat}{Γ : Context n}{Δ : Context m}{Θ : Context p} -> Sub Δ Θ -> Sub Γ Δ -> Sub Γ Θ
    _∘_ {zero} {_}{_} {ctxI nil'}      _  _		      = topS
    _∘_ {suc _}{_}{_} {ctxI (ext Γ A)} σ (subI (extSub' δ t)) =
      extSub (σ ∘ δ) (convert (substCompose σ δ A) (substTerm σ t))

    upS : {n : Nat}{Γ : Context n}{A : Type Γ} -> Sub Γ (Γ & A)
    upS = ?

    down : {n : Nat}{Γ : Context n}{A : Type Γ} -> Term Γ A -> Sub (Γ & A) Γ
    down t = extSub idS (convert substId t)

    -- Convertibility ---------------------------------------------------------

    _==_ : {n : Nat}{Γ : Context n} -> Type Γ -> Type Γ -> Prop
    A == B = ?

    refl : {n : Nat}{Γ : Context n}{A : Type Γ} -> A == A
    refl = ?

    cong : {n m : Nat}{Γ : Context n}{Δ : Context m}(f : Type Γ -> Type Δ)
	   {A B : Type Γ} -> A == B -> f A == f B
    cong f eq = ?

    _trans_ : {n : Nat}{Γ : Context n}{A B C : Type Γ} -> A == B -> B == C -> A == C
    ab trans bc = ?

    convert : {n : Nat}{Γ : Context n}{A B : Type Γ} -> A == B -> Term Γ B -> Term Γ A
    convert eq t = ?

    -- Properties -------------------------------------------------------------

    renameId : {n : Nat}{Γ : Context n}{A : Type Γ} -> rename idR A == A
    renameId = ?

    renameCompose : {n m p : Nat}{Γ : Context n}{Δ : Context m}{Θ : Context p}
		    (σ : Ren Δ Θ)(δ : Ren Γ Δ)(A : Type Γ) -> 
		    rename (σ coR δ) A == rename σ (rename δ A)
    renameCompose σ δ A = ?

    substId : {n : Nat}{Γ : Context n}{A : Type Γ} -> subst idS A == A
    substId = ?

    substCompose : {n m p : Nat}{Γ : Context n}{Δ : Context m}{Θ : Context p}
		   (σ : Sub Δ Θ)(δ : Sub Γ Δ)(A : Type Γ) -> 
		   subst (σ ∘ δ) A == subst σ (subst δ A)
    substCompose σ δ A = ?

    renameSubstCommute :
      {n m : Nat}{Γ : Context n}{Δ : Context m}{A : Type Γ}{B : Type (Γ & A)}
      {ρ : Ren Γ Δ}{t : Term Γ A} ->
      rename ρ (subst (down t) B) == subst (down (renameTerm ρ t)) (rename (liftR ρ) B)
    renameSubstCommute = ?


