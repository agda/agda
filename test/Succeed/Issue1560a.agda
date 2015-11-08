-- Shrunk version of examples/TT.agda
-- Bug introduced by fix of issue 1560

{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --no-termination-check #-}
-- {-# OPTIONS --no-positivity-check #-}

-- {-# OPTIONS -v tc.pos:10 #-}
-- {-# OPTIONS -v tc.polarity:30 #-}

data True : Set where
  tt : True

data ⊥ : Set where

infix 3 _/\_

data _/\_ (P Q : Set) : Set where
  andI : P -> Q -> P /\ Q

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- Finite sets ------------------------------------------------------------

data Suc (A : Set) : Set where
  fzero' : Suc A
  fsuc'  : A -> Suc A

mutual
  data Fin (n : Nat) : Set where
    finI : Fin' n -> Fin n

  Fin' : Nat -> Set
  Fin'  zero   = ⊥
  Fin' (suc n) = Suc (Fin n)

fsuc : {n : Nat} -> Fin n -> Fin (suc n)
fsuc i = finI (fsuc' i)

module FinEq where

  infix 5 _==_

  _==_ : {n : Nat} -> Fin n -> Fin n -> Set
  _==_ {suc _} (finI  fzero'  ) (finI  fzero'  ) = True
  _==_ {suc _} (finI (fsuc' i)) (finI (fsuc' j)) = i == j
  _==_          _                _               = ⊥

  -- Needed
  rewriteEq : {n : Nat}(C : Fin n -> Set){i j : Fin n} -> i == j -> C j -> C i
  rewriteEq {suc _} C {finI  fzero'  } {finI  fzero'  } eq x = x
  rewriteEq {suc _} C {finI (fsuc' i)} {finI (fsuc' j)} eq x = rewriteEq (\z -> C (fsuc z)) eq x
  rewriteEq {suc _} C {finI (fsuc' _)} {finI fzero'   } () _
  rewriteEq {suc _} C {finI fzero'   } {finI (fsuc' _)} () _
  rewriteEq {zero}  C {finI ()}        {_}              _  _

data Expr (n : Nat) : Set where
  eVar : Fin n -> Expr n
  eApp : Expr n -> Expr n -> Expr n

module ExprEq where

  infix 5 _==_

  _==_ : {n : Nat} -> Expr n -> Expr n -> Set
  eVar i     == eVar j     = FinEq._==_ i j
  eApp e1 e2 == eApp e3 e4 = e1 == e3 /\ e2 == e4
  _          == _          = ⊥

  rewriteEq : {n : Nat}(C : Expr n -> Set){r s : Expr n} -> r == s -> C s -> C r
  rewriteEq C {eVar i    } {eVar j    } eq x = FinEq.rewriteEq (\z -> C (eVar z)) eq x
  rewriteEq C {eApp e1 e2} {eApp e3 e4} (andI eq13 eq24) x =
    rewriteEq (\z -> C (eApp z e2)) eq13 (
      rewriteEq (\z -> C (eApp e3 z)) eq24 x
    )
  rewriteEq C {eVar _} {eApp _ _} () _
  rewriteEq C {eApp _ _} {eVar _  } () _


-- checking args of rewriteEq
-- args of rewriteEq =
--   [Mixed, Unused, Mixed, Mixed, Unused, StrictPos]
-- Computing polarity of Polarity.ExprEq.rewriteEq
-- Polarity of Polarity.ExprEq.rewriteEq from positivity:
--   [Invariant,Nonvariant,Invariant,Invariant,Nonvariant,Covariant]
-- Refining polarity with type  {n : Nat} (C : Expr n → Set)
--                              {r s : Expr n} →
--                              r == s → C s → C r
-- Polarity of Polarity.ExprEq.rewriteEq: [Invariant,Invariant,Invariant,Invariant,Nonvariant,Covariant]

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Polarity.hs:235

-- -}
-- -}
