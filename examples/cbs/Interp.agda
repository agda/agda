open import Proc

module Interp (param : Param) where

import Hear
open import Basics

private
  open module P = Process param
  open module H = Hear param

open Tran

data Result {a : U}(p : Proc a) : Set where
  speak  : forall {w q} -> p -! w !-> q -> Result p
  refuse : Silent p -> Result p

upR : {a b : U}{p : Proc b}(φ : Tran a b) -> Result p -> Result (φ /| p)
upR φ (speak  s) = speak  (tx-/| s)
upR φ (refuse s) = refuse (silent-/| s)

Oracle : Set
Oracle = Nat -> LR

prophecy : Oracle -> LR
prophecy ol = ol zero

nextOracle : Oracle -> Oracle
nextOracle ol = ol % suc

anyOracle : Oracle
anyOracle _ = left

ocons : LR -> Oracle -> Oracle
ocons l or zero    = l
ocons l or (suc n) = or n

step : {a : U}{p : Proc a} -> Guard p -> Oracle -> Result p
step og           _  = refuse silent-o
step (>g _)       _  = refuse silent->
step (w !g p)     _  = speak tx-!
step (w ! p +g f) _  = speak tx-+
step (defg x g)   ol with step g ol
... | refuse s1 = refuse (silent-def s1)
... | speak  s1 = speak (tx-def s1)
step (g1 ||g g2)  ol with step g1 (nextOracle ol)
                        | step g2 (nextOracle ol)
                        | prophecy ol
... | refuse s1 | refuse s2 | _     = refuse (silent-|| s1 s2)
... | speak s1  | refuse s2 | _     = speak (tx-!| s1 (sound g2))
... | refuse s1 | speak s2  | _     = speak (tx-|! (sound g1) s2)
... | speak s1  | speak _   | left  = speak (tx-!| s1 (sound g2))
... | speak _   | speak s2  | right = speak (tx-|! (sound g1) s2)
step (φ /|g g)    ol = upR φ (step g ol)
