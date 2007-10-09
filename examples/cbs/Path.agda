
module Path where

open import Basics hiding (_==_)
open import Proc
import Hear
import Interp

Node : Set
Node = Lift Nat

_==_ : Node -> Node -> Bool
bot          == bot          = true
lift zero    == lift zero    = true
lift (suc n) == lift (suc m) = lift n == lift m
_            == _            = false

data Name (a : True) : Set where
  fwd-edge : Nat -> Nat  -> Name a
  bwd-edge : Nat -> Node -> Name a
  start    : Nat -> Name a
  finish   : Nat -> Name a

data Msg : Set where
  forward  : Node -> Node -> Msg
  backward : Node -> Msg

T : True -> Set
T _ = Msg

module Impl where
  private module P = ProcDef True T Name
  open P hiding (_!_)

  P = Proc _

  infixr 40 _!_
  _!_ : Msg -> P -> P
  m ! p = P._!_ (lift m) p

  fwd : Nat -> Nat -> Msg
  fwd from to = forward (lift from) (lift to)

  fwd-runner : Nat -> Nat -> P
  fwd-runner from to = > react
    where
      react : Msg -> P
      react (forward from' to') =
        if   to' == lift from
        then fwd from to ! def (bwd-edge from from')
        else def (fwd-edge from to)
      react (backward _) = o

  bwd-runner : Nat -> Node -> P
  bwd-runner from w = > react
    where
      react : Msg -> P
      react (backward n) =
        if   n == w then o
        else if n == lift from
        then backward w ! o
        else def (bwd-edge from w)
      react (forward _ _) = def (bwd-edge from w)

  pitcher : Nat -> P
  pitcher n = forward bot (lift n) ! o 

  batter : Nat -> P
  batter n = > react
    where
      react : Msg -> P
      react (forward from to) =
        if   to == lift n
        then backward from ! o
        else def (start n)
      react _ = def (start n)

  env : Env
  env _ (fwd-edge from to) = fwd-runner from to
  env _ (bwd-edge from w)  = bwd-runner from w
  env _ (start n)          = batter n
  env _ (finish n)         = pitcher n

open Impl

param : Param
param = record
        { U    = True
        ; T    = T
        ; Name = Name
        ; env  = env
        }

private
  open module P = Process param
  open module H = Hear param
  open module I = Interp param