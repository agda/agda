
module Path where

open import Basics hiding (_==_)
open import Proc
import Graph

private open module G = Graph Nat

data Node : Set where
  node : Nat -> Node
  stop : Node

_==_ : Node -> Node -> Bool
stop         == stop         = true
node zero    == node zero    = true
node (suc n) == node (suc m) = node n == node m
_            == _            = false

data U : Set where
  int : U
  ext : U

data Name : Set where
  fwd-edge : Nat -> Nat  -> Name
  bwd-edge : Nat -> Node -> Name
  start    : Nat -> Name
  finish   : Nat -> Name

N : U -> Set
N int = Name
N ext = False

data Msg : Set where
  forward  : Node -> Node -> Msg
  backward : Node -> Msg

T : U -> Set
T int = Msg
T ext = Node

private
 module Impl where
  private module P = ProcDef U T N
  open P hiding (_!_)

  P = Proc int

  infixr 40 _!_
  _!_ : Msg -> P -> P
  m ! p = P._!_ (lift m) p

  fwd : Nat -> Nat -> Msg
  fwd from to = forward (node from) (node to)

  fwd-runner : Nat -> Nat -> P
  fwd-runner from to = > react
    where
      react : Msg -> P
      react (forward from' to') =
        if   to' == node from
        then fwd from to ! def (bwd-edge from from')
        else def (fwd-edge from to)
      react (backward _) = o

  bwd-runner : Nat -> Node -> P
  bwd-runner from w = > react
    where
      react : Msg -> P
      react (backward n) =
        if   n == w then o
        else if n == node from
        then backward w ! o
        else def (bwd-edge from w)
      react (forward _ _) = def (bwd-edge from w)

  pitcher : Nat -> P
  pitcher n = forward stop (node n) ! o 

  batter : Nat -> P
  batter n = > react
    where
      react : Msg -> P
      react (forward from to) =
        if   to == node n
        then backward from ! o
        else def (start n)
      react _ = def (start n)

  env : Env
  env int (fwd-edge from to) = fwd-runner from to
  env int (bwd-edge from w)  = bwd-runner from w
  env int (start n)          = batter n
  env int (finish n)         = pitcher n
  env ext ()

  edges : Graph -> P
  edges [] = o
  edges (edge x y :: G) = def (fwd-edge x y) || edges G

  φ : Tran ext int
  φ = record { upV = up; downV = down }
    where
      down : Node -> Lift Msg
      down x = lift (backward x)

      up : Msg -> Lift Node
      up (forward _ _) = bot
      up (backward x)  = lift x

  main : Graph -> Nat -> Nat -> Proc ext
  main G x y = φ /| def (finish y) || def (start x) || edges G

open Impl public

param : Param
param = record
        { U    = U
        ; T    = T
        ; Name = N
        ; env  = env
        }
