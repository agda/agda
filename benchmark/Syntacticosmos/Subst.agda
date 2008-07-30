module Subst (Gnd : Set)(U : Set)(El : U -> Set) where

open import Basics
open import Pr
open import Nom
import Kind
open Kind Gnd U El
import Cxt
open Cxt Kind
import Loc
open Loc Kind
import Term
open Term Gnd U El
import Shift
open Shift Gnd U El
import Inst
open Inst Gnd U El

data _-[_]_ : Cxt -> Kind -> Cxt -> Set where
  ES : {D : Cxt}{C : Kind} -> EC -[ C ] D
  _[_-_:=_] : {G D : Cxt}{C : Kind} -> (G -[ C ] D) ->
              (x : Nom){Gx : [| G Hasn't x |]}(S : Kind) ->
              D [! C !]- S ->
              (G [ x - S ]){Gx} -[ C ] D

fetch : {G D : Cxt}{C S : Kind} -> (G -[ C ] D) ->
        Nom :- GooN G S -> D [! C !]- S
fetch ES [ x / () ]
fetch (g [ x - S := s ]) [ y / p ] with nomEq x y
fetch (g [ x - S := s ]) [ .x / refl ] | yes refl = s
fetch (g [ x - S := s ]) [ y / p ]     | no n = fetch g [ y / p ]

closed : {G : Cxt}{L : Loc}{T : Kind} ->
         G [ EL / Head ]- T  ->  G [ L / Head ]- T
closed (` x -! xg) = ` x -! xg
closed (# () -! _)

mutual

  wsubst : {C : Kind}{G D : Cxt} -> (G -[ C ] D) ->
          {L : Loc}{T : Kind}(t : L [ Term C ]- T) -> [| Good G t |] ->
          D [ L / Term C ]- T
  wsubst g [ s ] sg = G[ wsubsts g s sg ]
  wsubst g (fn A f) fg = Gfn A \ a -> wsubst g (f a) (fg a)
  wsubst g (\\ b)    bg = G\\ (wsubst g b bg)
  wsubst g (# v $ s) pg = (# v -! _) G$ wsubsts g s (snd pg)
  wsubst g (` x $ s) pg =
    go (shift closed (fetch g [ x / fst pg ])) (wsubsts g s (snd pg))

  wsubsts : {C : Kind}{G D : Cxt} -> (G -[ C ] D) ->
           {L : Loc}{Z : Gnd}{S : Kind}
           (s : L [ Args C Z ]- S) -> [| Good G s |] ->
           D [ L / Args C Z ]- S
  wsubsts g (a ^ s)   sg = a G^ wsubsts g s sg
  wsubsts g (r & s)   pg = wsubst g r (fst pg) G& wsubsts g s (snd pg)
  wsubsts g nil       _  = Gnil

subst : {C : Kind}{G D : Cxt} -> (G -[ C ] D) ->
        {L : Loc}{T : Kind} -> G [ L / Term C ]- T -> D [ L / Term C ]- T
subst g (t -! tg) = wsubst g t tg

