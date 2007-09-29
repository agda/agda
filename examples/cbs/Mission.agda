
open import Proc

module Mission (param : Param) where

import Interp
import Receipt
import Silence
open import Basics

private
  open module P = Process param
  open module I = Interp param
  open module S = Silence param
  open module R = Receipt param
    renaming ( sound    to hear-sound
             ; uniq     to hear-uniq
             ; complete to hear-complete
             )

open Tran

Sound : {a : U} -> Proc a -> Result a -> Set
Sound p (w / q) = p -! w !⟶ q
Sound p refuse  = Silent p

sound : {a : U}{p : Proc a}(g : Guard p)(oracle : Oracle) ->
        Sound p (step g oracle)
sound og           oracle = silent-o
sound (>g f)       oracle = silent->
sound (w !g p)     oracle = tx-!
sound (w ! p +g f) oracle = tx-+
sound (g₁ ||g g₂)  oracle with step g₁ (nextOracle oracle)
                             | sound g₁ (nextOracle oracle)
                             | step g₂ (nextOracle oracle)
                             | sound g₂ (nextOracle oracle)
                             | prophecy oracle
... | refuse | s₁ | refuse | s₂ | _     = silent-|| s₁ s₂
... | w / p  | s₁ | refuse | s₂ | _     = tx-!| s₁ (hear-sound g₂)
... | refuse | s₁ | w / p  | s₂ | _     = tx-|! (hear-sound g₁) s₂
... | w / p  | s₁ | _ / _  | s₂ | left  = tx-!| s₁ (hear-sound g₂)
... | _ / _  | s₁ | w / p  | s₂ | right = tx-|! (hear-sound g₁) s₂
sound (φ /|g g)    oracle with step g oracle
                             | sound g oracle
... | w / p  | s = tx-/| s
... | refuse | s = silent-/| s
sound (defg x g)   oracle with step g oracle
                             | sound g oracle
... | w / p  | s = tx-def s
... | refuse | s = silent-def s

Refuse : {a : U} -> Result a -> Set
Refuse (_ / _) = False
Refuse refuse  = True

completeS : {a : U}{p : Proc a}(g : Guard p) ->
           Silent p -> (oracle : Oracle) -> Refuse (step g oracle)
completeS og           silent-o          oracle = tt
completeS (>g f)       silent->          oracle = tt
completeS (_ !g _)     ()                oracle
completeS (_ ! _ +g _) ()                oracle
completeS (g₁ ||g g₂)  (silent-|| s₁ s₂) oracle with step g₁ (nextOracle oracle)
                                                   | completeS g₁ s₁ (nextOracle oracle)
                                                   | step g₂ (nextOracle oracle)
                                                   | completeS g₂ s₂ (nextOracle oracle)
                                                   | prophecy oracle
... | refuse | _  | refuse | _  | _     = tt
... | w / p  | ih | refuse | _  | _     = ih
... | refuse | _  | w / p  | ih | _     = ih
... | w / p  | ih | _ / _  | _  | left  = ih
... | _ / _  | _  | w / p  | ih | right = ih
completeS (φ /|g g)    (silent-/| s)  oracle with step g oracle
                                                | completeS g s oracle
... | w / p  | ih = ih
... | refuse | ih = tt
completeS (defg x g)   (silent-def s) oracle with step g oracle
                                                | completeS g s oracle
... | w / p  | ih = ih
... | refuse | ih = tt

theOracle : {a : U}{p : Proc a}{w : LT a}{q : Proc a} ->
            p -! w !⟶ q -> Oracle
theOracle tx-!        = anyOracle
theOracle tx-+        = anyOracle
theOracle (tx-!| s r) = left  :: theOracle s
theOracle (tx-|! r s) = right :: theOracle s
theOracle (tx-/| s)   = theOracle s
theOracle (tx-def s)  = theOracle s

completeT : {a : U}{p : Proc a}(g : Guard p){w : LT a}{q : Proc a} ->
            (r : p -! w !⟶ q) -> w / q == step g (\x -> theOracle r x)
completeT og           ()
completeT (>g _)       ()
completeT (w !g p)     tx-!        = refl
completeT (w ! p +g f) tx-+        = refl
completeT (g₁ ||g  g₂) (tx-!| s r) with step g₁ (\x -> theOracle s x)
                                      | step g₂ (\x -> theOracle s x)
                                      | completeT g₁ s
                                      | hear-complete g₂ r
... | .(_ / _) | refuse | refl | refl = refl
... | .(_ / _) | _ / _  | refl | refl = refl
completeT (g₁ ||g  g₂) (tx-|! r s) with step g₁ (\x -> theOracle s x)
                                      | step g₂ (\x -> theOracle s x)
                                      | hear-complete g₁ r
                                      | completeT g₂ s
... | refuse | .(_ / _) | refl | refl = refl
... | _ / _  | .(_ / _) | refl | refl = refl
completeT (φ /|g g) (tx-/| s) with step g (\x -> theOracle s x)
                                 | completeT g s
... | ._ | refl = refl
completeT (defg x g)  (tx-def s) = completeT g s
