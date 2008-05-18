
module Proof where

open import Basics hiding (_==_)
open import Proc
open import Path
import Graph

private
  open module G = Graph Nat
  open module P = Process param hiding (U; T; _!_)

{-

Soundness:

  if we get an answer there is a path

Completeness:

  if there is a path we get an answer

-}

infix 18 _encodes_

data _encodes_ {G : Graph} :
      {x y : Nat} -> List Node -> Path G x y -> Set where
  nul-path  : {x : Nat} -> stop :: [] encodes nul {x = x}
  step-path : {x y z : Nat}{xs : List Node}
              {step : Step G x y}{path : Path G y z} ->
              xs encodes path ->
              node y :: xs encodes step <> path

test : {G : Graph}{a b c : Nat}
       {ab : Step G a b}{bc : Step G b c} ->
       node b :: node c :: stop :: [] encodes
       ab <> bc <> nul
test = step-path (step-path nul-path)

target : {G : Graph}{x y : Nat} -> Step G x y -> Nat
target {y = y} _ = y

encoding : {G : Graph}{x y : Nat} -> Path G x y -> List Node
encoding nul            = stop :: []
encoding (step <> path) = node (target step) :: encoding path

lem-encode : {G : Graph}{x y : Nat}(path : Path G x y) ->
             encoding path encodes path
lem-encode nul            = nul-path
lem-encode (step <> path) = step-path (lem-encode path)

data WellFormed : List Node -> Set where
  good-stop : WellFormed (stop :: [])
  good-::   : forall {x xs} -> WellFormed xs -> WellFormed (node x :: xs)

data MalFormed : List Node -> Set where
  bad-[]   : MalFormed []
  bad-::   : forall {x xs} -> MalFormed xs -> MalFormed (node x :: xs)
  bad-stop : forall {x xs} -> MalFormed (stop :: x :: xs)

module Theorems (G : Graph)(start end : Nat) where

  mainp = main G start end

  Complete : Set
  Complete = (path : Path G start end) ->
             ∃ \q -> Silent q /\
                     mainp -! encoding path !->* q

  Sound : Set
  Sound = forall q xs -> Silent q -> WellFormed xs ->
          mainp -! xs !->* q ->
          ∃ \(path : Path G start end) -> xs encodes path

  Sound-Fail : Set
  Sound-Fail = forall q xs -> Silent q -> MalFormed xs ->
               mainp -! xs !->* q -> Path G start end -> False

silent-edges : {a : U} -> Graph -> Proc a
silent-edges []       = o
silent-edges (_ :: G) = o || silent-edges G

silent-silent-edges : {a : U}(G : Graph) -> Silent (silent-edges {a} G)
silent-silent-edges []       = silent-o
silent-silent-edges (_ :: G) = silent-|| silent-o (silent-silent-edges G)

module Proofs (G : Graph) where

  private open module T = Theorems G

  complete : (start end : Nat) -> Complete start end
  complete x .x nul =
    ∃-intro q (silent-q , run)
    where
      edg₁ = {! !}
      edg₂ = {! !}
      edg₃ = silent-edges G

      silent-edg₃ : Silent edg₃
      silent-edg₃ = silent-silent-edges G

      q = φ /| o || o || edg₃

      silent-q : Silent q
      silent-q = silent-/| (silent-|| silent-o (silent-|| silent-o silent-edg₃))

      rx-edg₁ : edges G -[ lift (forward stop (node x)) ]-> edg₁
      rx-edg₁ = {! !}

      rx-edg₂ : edg₁ -[ {! !} ]-> edg₂
      rx-edg₂ = {! !}

      run-edg₃ : φ /| o || o || edg₂ -! [] !->* φ /| o || o || edg₃
      run-edg₃ = {! !}

      tx-batter : (n : Nat) ->
                  if node n == node n
                  then backward stop ! o
                  else def (start x)
                  -! lift (backward stop) !-> o
      tx-batter zero    = tx-!
      tx-batter (suc n) = tx-batter n

      run : mainp x x -! stop :: [] !->* q
      run = (tx-/| (tx-!|
              (tx-def tx-!)
              (rx-|| (rx-def rx->) rx-edg₁)))
            >*>
            (tx-/| (tx-|! rx-o (tx-!| (tx-batter x) rx-edg₂)))
            >!>
            run-edg₃
