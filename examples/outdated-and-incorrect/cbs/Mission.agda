
open import Proc

module Mission (param : Param) where

import Interp
import Hear
open import Basics

private
  open module P = Process param
  open module I = Interp param
  open module H = Hear param
    renaming ( sound    to hear-sound
             ; uniq     to hear-uniq
             ; complete to hear-complete
             )


open Tran

data IsRefuse {a : U}{p : Proc a} : Result p -> Set where
  isRefuse : {s : Silent p} -> IsRefuse (refuse s)

completeS : {a : U}{p : Proc a}(g : Guard p) ->
           Silent p -> (oracle : Oracle) -> IsRefuse (step g oracle)
completeS og           silent-o          oracle = isRefuse
completeS (>g f)       silent->          oracle = isRefuse
completeS (_ !g _)     ()                oracle
completeS (_ ! _ +g _) ()                oracle
completeS (g1 ||g g2)  (silent-|| s1 s2) oracle
  with step g1 (nextOracle oracle)
       | completeS g1 s1 (nextOracle oracle)
       | step g2 (nextOracle oracle)
       | completeS g2 s2 (nextOracle oracle)
       | prophecy oracle
... | refuse _ | _  | refuse _ | _  | _     = isRefuse
... | speak _  | () | speak _  | _  | _
... | refuse _ | _  | speak _  | () | _
... | speak _  | () | speak _  | _  | left
... | speak _  | _  | speak _  | () | right
... | speak _  | _  | refuse _ | () | _
completeS (φ /|g g)    (silent-/| s)  oracle with step g oracle
                                                | completeS g s oracle
... | speak _  | ()
... | refuse _ | _ = isRefuse
completeS (defg x g)   (silent-def s) oracle with step g oracle
                                                | completeS g s oracle
... | speak _  | ()
... | refuse _ | _ = isRefuse

theOracle : {a : U}{p : Proc a}{w : LT a}{q : Proc a} ->
            p -! w !-> q -> Oracle
theOracle tx-!        = anyOracle
theOracle tx-+        = anyOracle
theOracle (tx-!| s r) = ocons left  (theOracle s)
theOracle (tx-|! r s) = ocons right (theOracle s)
theOracle (tx-/| s)   = theOracle s
theOracle (tx-def s)  = theOracle s

data IsSpeak {a : U}{p : Proc a}(w : LT a)(q : Proc a) : Result p -> Set where
  isSpeak : {r : p -! w !-> q} -> IsSpeak w q (speak r)

completeT : {a : U}{p : Proc a}(g : Guard p){w : LT a}{q : Proc a} ->
            (r : p -! w !-> q) -> IsSpeak w q (step g (\x -> theOracle r x))
completeT og           ()
completeT (>g _)       ()
completeT (w !g p)     tx-!        = isSpeak
completeT (w ! p +g f) tx-+        = isSpeak
completeT (g1 ||g  g2) (tx-!| s r) with step g1 (\x -> theOracle s x)
                                      | step g2 (\x -> theOracle s x)
                                      | completeT g1 s
                                      | hear-complete g2 r
... | .(speak _) | refuse _ | isSpeak | refl = isSpeak
... | .(speak _) | speak _  | isSpeak | refl = isSpeak
completeT (g1 ||g  g2) (tx-|! r s) with step g1 (\x -> theOracle s x)
                                      | step g2 (\x -> theOracle s x)
                                      | hear-complete g1 r
                                      | completeT g2 s
... | refuse _ | .(speak _) | refl | isSpeak = isSpeak
... | speak _  | .(speak _) | refl | isSpeak = isSpeak
completeT (φ /|g g) (tx-/| s) with step g (\x -> theOracle s x)
                                 | completeT g s
... | ._ | isSpeak = isSpeak
completeT (defg x g)  (tx-def s) with step g (\x -> theOracle s x)
                                    | completeT g s
... | ._ | isSpeak = isSpeak


