
open import Proc

module Silence (param : Param) where

open import Basics
import Interp
import Hear

open Process param
open Interp param
open Hear param

NoSpeak : {a : U} -> Proc a -> Set
NoSpeak {a} p = (w : LT a)(q : Proc a) -> ¬ (p -! w !-> q)

silent-nospeak : {a : U}{p : Proc a} -> Silent p -> NoSpeak p
silent-nospeak silent-o          w  q  ()
silent-nospeak silent->          w  q  ()
silent-nospeak (silent-|| s1 s2) w  ._ (tx-!| h _) = silent-nospeak s1 _ _ h
silent-nospeak (silent-|| s1 s2) w  ._ (tx-|! _ h) = silent-nospeak s2 _ _ h
silent-nospeak (silent-def s)    w  q  (tx-def h)  = silent-nospeak s _ _ h
silent-nospeak (silent-/| s)     ._ ._ (tx-/| h)   = silent-nospeak s _ _ h

nospeak-silent : {a : U}{p : Proc a} -> Guard p -> NoSpeak p -> Silent p
nospeak-silent og           s = silent-o
nospeak-silent (>g f)       s = silent->
nospeak-silent (w !g p)     s = kill (s _ _ tx-!)
nospeak-silent (w ! p +g f) s = kill (s _ _ tx-+)
nospeak-silent (g1 ||g g2)  s =
    silent-|| (nospeak-silent g1 (inv1 g2 s))
              (nospeak-silent g2 (inv2 g1 s))
  where
    module Inv {a : U}{p1 p2 : Proc a} where
      inv1 : Guard p2 -> NoSpeak (p1 || p2) -> NoSpeak p1
      inv1 g2 h w p t = h _ _ (tx-!| t (sound g2))

      inv2 : Guard p1 -> NoSpeak (p1 || p2) -> NoSpeak p2
      inv2 g1 h w p t = h _ _ (tx-|! (sound g1) t)
    open Inv
nospeak-silent (φ /|g g)    s = silent-/| (nospeak-silent g (inv s))
  where
    inv : forall {p} -> NoSpeak (φ /| p) -> NoSpeak p
    inv h w p t = h _ _ (tx-/| t)
nospeak-silent (defg x g)   s = silent-def (nospeak-silent g (inv s))
  where
    inv : NoSpeak (def x) -> NoSpeak (env _ x)
    inv h w p t = h _ _ (tx-def t)
