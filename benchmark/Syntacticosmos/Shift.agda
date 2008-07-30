module Shift (Gnd : Set)(U : Set)(El : U -> Set) where

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

popH : {D : Cxt}{M : Loc}{S T : Kind} ->
       D [ M / Head ]- T -> D [ M * S / Head ]- T
popH ( ` x -! xg )  = ` x -! xg
popH ( # v -! _ )   = # (pop v) -! _

weak : {G D : Cxt}{L M : Loc}{S : Kind} ->
       ({T : Kind} -> G [ L / Head ]- T -> D [ M / Head ]- T) ->
       {T : Kind} -> G [ L * S / Head ]- T -> D [ M * S / Head ]- T
weak rho (` x -! p )        = popH (rho (` x -! p))
weak rho (# top -! _ )      = # top -! _ 
weak rho (# (pop v) -! _ )  = popH (rho (# v -! _))

shift : {G D : Cxt}{L M : Loc} ->
  ({T : Kind} -> G [ L / Head ]- T -> D [ M / Head ]- T) ->
  {j : Jud}{T : Kind} -> G [ L / j ]- T  ->  D [ M / j ]- T
shift {G} {D} rho (t -! tg) = chug rho t tg where
  chug : {j : Jud}{L M : Loc} ->
    ({T : Kind} -> G [ L / Head ]- T -> D [ M / Head ]- T) ->
    {T : Kind}(t : L [ j ]- T) -> [| Good G t |] ->  D [ M / j ]- T
  chug {Head} rho h hg = rho ( h -! hg )
  chug rho [ s ] sg = G[ chug rho s sg ]
  chug rho (fn A f) fg = Gfn A (\ a -> chug rho (f a) (fg a))
  chug rho (\\ b) bg = G\\ (chug (weak rho) b bg)
  chug rho (a ^ s) sg = a G^ chug rho s sg
  chug rho (r & s) rsg = chug rho r (fst rsg) G& chug rho s (snd rsg)
  chug rho nil _ = Gnil
  chug rho (h $ s) hsg = chug rho h (fst hsg) G$ chug rho s (snd hsg)

bind : {G : Cxt}(x : Nom){Gx : [| G Hasn't x |]}{S : Kind}{j : Jud}{T : Kind} ->
       (G [ x - S ]) {Gx} [ EL / j ]- T -> G [ EL * S / j ]- T
bind {G} x {Gx}{S} = shift topx where
  topx : {T : Kind} -> (G [ x - S ]) {Gx} [ EL / Head ]- T ->
         G [ EL * S / Head ]- T
  topx (` y -! yg) with nomEq x y
  topx (` .x -! refl) | yes refl = # top -! _
  topx (` y -! yg)    | no _     = ` y -! yg
  topx (# () -! _)
