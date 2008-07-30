module Eta (Gnd : Set)(U : Set)(El : U -> Set) where

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

data Sawn (G : Cxt)(C : Kind)(L : Loc)(R : Kind) : Kind -> Set where
  snil : Sawn G C L R R
  scons : {S T : Kind} -> Sawn G C L R (S |> T) ->
                          G [ L / Term C ]- S ->
                          Sawn G C L R T
  sarg : {A : U}{K : El A -> Kind} ->
         Sawn G C L R (Pi A K) -> (a : El A) ->
         Sawn G C L R (K a)

stitch : {G : Cxt}{C : Kind}{Z : Gnd}{L : Loc}{R S : Kind} ->
         Sawn G C L R S -> G [ L / Args C Z ]- S -> G [ L / Args C Z ]- R
stitch snil s = s
stitch (scons r s) t = stitch r (s G& t)
stitch (sarg r a) t = stitch r (a G^ t)

sawsh : {G : Cxt}{C : Kind}{L M : Loc} ->
        ({T : Kind} -> G [ L / Head ]- T -> G [ M / Head ]- T) ->
        {R S : Kind} -> Sawn G C L R S -> Sawn G C M R S
sawsh rho snil = snil
sawsh rho (scons r s) = scons (sawsh rho r) (shift rho s)
sawsh rho (sarg r a) = sarg (sawsh rho r) a

long : {G : Cxt}{C : Kind}{L : Loc}(S : Kind){T : Kind} ->
       G [ L / Head ]- T ->
       Sawn G C L T S ->
       G [ L / Term C ]- S
long (Ty Z)   h s = h G$ (stitch s Gnil) 
long (Pi A K) h s = Gfn A \ a -> long (K a) h (sarg s a)  
long (S |> T) h s =
  G\\ (long T (popH h) (scons (sawsh popH s) (long S (# top -! _) snil))) 

var : {G : Cxt}{C : Kind}(x : Nom){Gx : [| G Has x |]} ->
      G [ EL / Term C ]- (wit ((G ?- x) {Gx}))
var {G} x {Gx} with (G ?- x) {Gx}
... | [ T / g ] = long T (` x -! g) snil
