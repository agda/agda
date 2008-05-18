
module ProofRep where

import Prelude
import Logic.Relations
import Logic.Identity
import Data.Nat
import Data.Nat.Properties

open Prelude
open Data.Nat hiding (_==_; _≡_)
open Data.Nat.Properties
open Logic.Relations

module Foo (Var : Set) where

  data _==_ : (x y : Var) -> Set where
    cRefl  : {x : Var} -> x == x
    cSym   : {x y : Var} -> y == x -> x == y
    cTrans : {x y z : Var} -> x == z -> z == y -> x == y
    cAxiom : {x y : Var} -> x == y

  data Axioms {A : Set}(_≈_ : Rel A)([_] : Var -> A) : Set where
    noAxioms   : Axioms _≈_ [_]
    anAxiom    : (x y : Var) -> [ x ] ≈ [ y ] -> Axioms _≈_ [_]
    manyAxioms : Axioms _≈_ [_] -> Axioms _≈_ [_] -> Axioms _≈_ [_]

  refl : {x : Var} -> x == x
  refl = cRefl

  sym : {x y : Var} -> x == y -> y == x
  sym (cRefl xy)     = cRefl (Var.sym xy)
  sym  cAxiom        = cSym cAxiom
  sym (cSym p)       = p
  sym (cTrans z p q) = cTrans z (sym q) (sym p)

  trans : {x y z : Var} -> x == y -> y == z -> x == z
  trans {x}{y}{z} (cRefl xy) q     = Var.subst (\w -> w == z) (Var.sym xy) q
  trans {x}{y}{z} p (cRefl yz)     = Var.subst (\w -> x == w) yz p
  trans {x}{y}{z} (cTrans w p q) r = cTrans w p (trans q r)
  trans           p q              = cTrans _ p q

