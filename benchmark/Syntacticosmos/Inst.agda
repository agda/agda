module Inst (Gnd : Set)(U : Set)(El : U -> Set) where

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

mutual
  winst : {G : Cxt}{C : Kind}{L : Loc}{I : Kind}
          (x : L ! I) -> G [ L bar x / Term C ]- I ->
          {T : Kind}(t : L [ Term C ]- T) -> [| Good G t |] ->
          G [ L bar x / Term C ]- T
  winst x i [ s ]     sg = G[ winsts x i s sg ]
  winst x i (fn A f)  fg = Gfn A \ a -> winst x i (f a) (fg a)
  winst x i (\\ b)    bg = G\\ (winst (pop x) (shift popH i) b bg)
  winst x i (h $ s)   pg = wing x i h (fst pg) (winsts x i s (snd pg)) 

  winsts : {G : Cxt}{C : Kind}{L : Loc}{Z : Gnd}{I : Kind}
           (x : L ! I) -> G [ L bar x / Term C ]- I ->
           {T : Kind}(s : L [ Args C Z ]- T) -> [| Good G s |] ->
           G [ L bar x / Args C Z ]- T
  winsts x i (a ^ s)   sg = a G^ winsts x i s sg
  winsts x i (r & s)   pg = winst x i r (fst pg) G& winsts x i s (snd pg)
  winsts x i nil       _  = Gnil

  wing : {G : Cxt}{C : Kind}{L : Loc}{Z : Gnd}{I : Kind}
         (x : L ! I) -> G [ L bar x / Term C ]- I ->
         {T : Kind}(h : L [ Head ]- T) -> [| Good G h |] ->
         G [ L bar x / Args C Z ]- T ->
         G [ L bar x / Term C ]- Ty Z
  wing x i (` k)     kg s = (` k -! kg) G$ s
  wing x i (# y)     _  s with varQV x y
  wing x i (# .x)    _  s  | vSame = go i s
  wing x i (# .(x thin y)) _ s | vDiff y = (# y -! _) G$ s

  go : {G : Cxt}{C : Kind}{L : Loc}{Z : Gnd}{I : Kind} ->
       G [ L / Term C ]- I -> G [ L / Args C Z ]- I ->
       G [ L / Term C ]- Ty Z
  go (fn A f -! fg) ((a ^ s) -! sg) = go (f a -! fg a) (s -! sg)
  go (\\ b -! bg) ((r & s) -! pg) =
    go (winst top (r -! fst pg) b bg) (s -! snd pg)
  go t (nil -! _) = t

inst : {G : Cxt}{C : Kind}{L : Loc}{I : Kind}
       (x : L ! I) -> G [ L bar x / Term C ]- I ->
       {T : Kind} -> G [ L / Term C ]- T -> G [ L bar x / Term C ]- T
inst x i (t -! tg) = winst x i t tg

_$$_ : {G : Cxt}{C S T : Kind}{L : Loc} ->
       G [! C !]- (S |> T) -> G [! C !]- S -> G [! C !]- T
(\\ b -! bg) $$ sg = inst top sg (b -! bg)

