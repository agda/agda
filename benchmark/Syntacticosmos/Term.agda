module Term (Gnd : Set)(U : Set)(El : U -> Set) where

open import Basics
open import Pr
open import Nom
import Kind
open module KindGUEl = Kind Gnd U El
import Loc
open module LocK = Loc Kind
import Cxt
open module CxtK = Cxt Kind

data Jud : Set where
  Term : Kind -> Jud
  Args : Kind -> Gnd -> Jud
  Head : Jud

data _[_]-_ : Loc -> Jud -> Kind -> Set where
  [_] : {C : Kind}{L : Loc}{Z : Gnd} ->
        L [ Args C Z ]- C  ->  L [ Term C ]- Ty Z
  fn : {C : Kind}{L : Loc}(A : U){K : El A -> Kind} ->
       ((x : El A) -> L [ Term C ]- K x) -> L [ Term C ]- Pi A K
  \\ : {C : Kind}{L : Loc}{S T : Kind} ->
       (L * S) [ Term C ]- T  ->  L [ Term C ]- (S |> T)
  _^_ : {C : Kind}{L : Loc}{Z : Gnd}{A : U}{K : El A -> Kind} ->
        (x : El A) -> L [ Args C Z ]- K x -> L [ Args C Z ]- Pi A K
  _&_ : {C : Kind}{L : Loc}{S T : Kind}{Z : Gnd} ->
        L [ Term C ]- S  ->  L [ Args C Z ]- T  ->  L [ Args C Z ]- (S |> T)
  nil : {C : Kind}{L : Loc}{Z : Gnd} -> L [ Args C Z ]- Ty Z
  _$_ : {C : Kind}{L : Loc}{T : Kind}{Z : Gnd} ->
        L [ Head ]- T  ->  L [ Args C Z ]- T  ->  L [ Term C ]- Ty Z
  ` : Nom -> {S : Kind}{L : Loc} -> L [ Head ]- S
  # : {L : Loc}{S : Kind} -> L ! S -> L [ Head ]- S

infixr 90 _^_ _&_

infix 40 _[_]-_

Good : Cxt -> {L : Loc}{j : Jud}{T : Kind} -> L [ j ]- T -> Pr
Good G [ c ]      = Good G c
Good G (fn A f)   = all (El A) \a -> Good G (f a)
Good G (\\ b)     = Good G b
Good G (a ^ ss)   = Good G ss
Good G (s & ss)   = Good G s /\ Good G ss
Good G nil        = tt
Good G (x $ ss)   = Good G x /\ Good G ss
Good G (` x {S})  = GooN G S x
Good G (# v)      = tt

data _[_/_]-_ (G : Cxt)(L : Loc)(j : Jud)(T : Kind) : Set where
  _-!_ : (t : L [ j ]- T) -> [| Good G t |] -> G [ L / j ]- T

gtm : {G : Cxt}{L : Loc}{j : Jud}{T : Kind} -> G [ L / j ]- T -> L [ j ]- T
gtm (t -! _) = t

good : {G : Cxt}{L : Loc}{j : Jud}{T : Kind}
       (t : G [ L / j ]- T) -> [| Good G (gtm t) |]
good (t -! g) = g


_[!_!]-_ : Cxt -> Kind -> Kind -> Set
G [! C !]- T = G [ EL / Term C ]- T

G[_] : {G : Cxt}{C : Kind}{L : Loc}{Z : Gnd} ->
       G [ L / Args C Z ]- C ->
     ----------------------------
       G [ L / Term C ]- Ty Z

G[ c -! cg ] = [ c ] -! cg

Gfn : {G : Cxt}{C : Kind}{L : Loc}(A : U){K : El A -> Kind} ->
      ((x : El A) -> G [ L / Term C ]- K x) ->
    -------------------------------------------
      G [ L / Term C ]- Pi A K

Gfn A f = fn A (gtm o f) -! (good o f)

G\\ : {G : Cxt}{C : Kind}{L : Loc}{S T : Kind} ->
      G [ L * S / Term C ]- T ->
    ------------------------------
      G [ L / Term C ]- (S |> T)

G\\ (b -! bg) = \\ b -! bg

_G^_ : {G : Cxt}{C : Kind}{L : Loc}{Z : Gnd}{A : U}{K : El A -> Kind} ->
       (x : El A) ->
       G [ L / Args C Z ]- K x ->
     ------------------------------
       G [ L / Args C Z ]- Pi A K

a G^ (s -! sg) = (a ^ s) -! sg

_G&_ : {G : Cxt}{C : Kind}{L : Loc}{S T : Kind}{Z : Gnd} ->
        G [ L / Term C ]- S  ->
        G [ L / Args C Z ]- T  ->
      ----------------------------------
        G [ L / Args C Z ]- (S |> T)

(r -! rg) G& (s -! sg) = (r & s) -! (rg , sg)

Gnil : {G : Cxt}{C : Kind}{L : Loc}{Z : Gnd} ->
      -----------------------------
        G [ L / Args C Z ]- Ty Z

Gnil = nil -! _

_G$_ : {G : Cxt}{C : Kind}{L : Loc}{T : Kind}{Z : Gnd} ->
        G [ L / Head ]- T  -> 
        G [ L / Args C Z ]- T  ->
      -----------------------------
        G [ L / Term C ]- Ty Z

(h -! hg) G$ (s -! sg) = (h $ s) -! (hg , sg)

G` :   {G : Cxt}{S : Kind}{L : Loc} -> Nom :- GooN G S ->
     ------------------------------------------------------
        G [ L / Head ]- S

G` [ x / xg ] = ` x -! xg

G# : {G : Cxt}{L : Loc}{S : Kind} -> L ! S ->
     --------------------------
       G [ L / Head ]- S

G# v = # v -! _

infixr 90 _G^_ _G&_

