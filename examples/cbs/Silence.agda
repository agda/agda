
open import Proc

module Silence (param : Param) where

open import Basics
import Interp
import Hear

private
  open module P = Process param
  open module I = Interp param
  open module H = Hear param

NoSpeak : {a : U} -> Proc a -> Set
NoSpeak {a} p = (w : LT a)(q : Proc a) -> ¬ (p -! w !⟶ q)

silent-nospeak : {a : U}{p : Proc a} -> Silent p -> NoSpeak p
silent-nospeak silent-o          w  q  ()
silent-nospeak silent->          w  q  ()
silent-nospeak (silent-|| s₁ s₂) w  ._ (tx-!| h _) = silent-nospeak s₁ _ _ h
silent-nospeak (silent-|| s₁ s₂) w  ._ (tx-|! _ h) = silent-nospeak s₂ _ _ h
silent-nospeak (silent-def s)    w  q  (tx-def h)  = silent-nospeak s _ _ h
silent-nospeak (silent-/| s)     ._ ._ (tx-/| h)   = silent-nospeak s _ _ h

nospeak-silent : {a : U}{p : Proc a} -> Guard p -> NoSpeak p -> Silent p
nospeak-silent og           s = silent-o
nospeak-silent (>g f)       s = silent->
nospeak-silent (w !g p)     s = kill (s _ _ tx-!)
nospeak-silent (w ! p +g f) s = kill (s _ _ tx-+)
nospeak-silent (g₁ ||g g₂)  s =
    silent-|| (nospeak-silent g₁ (inv₁ g₂ s))
              (nospeak-silent g₂ (inv₂ g₁ s))
  where
    module Inv {a : U}{p₁ p₂ : Proc a} where
      inv₁ : Guard p₂ -> NoSpeak (p₁ || p₂) -> NoSpeak p₁
      inv₁ g₂ h w p t = h _ _ (tx-!| t (sound g₂))

      inv₂ : Guard p₁ -> NoSpeak (p₁ || p₂) -> NoSpeak p₂
      inv₂ g₁ h w p t = h _ _ (tx-|! (sound g₁) t)
    open Inv
nospeak-silent (φ /|g g)    s = silent-/| (nospeak-silent g (inv s))
  where
    inv : forall {p} -> NoSpeak (φ /| p) -> NoSpeak p
    inv h w p t = h _ _ (tx-/| t)
nospeak-silent (defg x g)   s = silent-def (nospeak-silent g (inv s))
  where
    inv : NoSpeak (def x) -> NoSpeak (env _ x)
    inv h w p t = h _ _ (tx-def t)
