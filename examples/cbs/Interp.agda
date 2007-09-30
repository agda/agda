open import Proc

module Interp (param : Param) where

import Hear
open import Basics

private
  open module P = Process param
  open module H = Hear param

open Tran

data Result {a : U}(p : Proc a) : Set where
  speak  : forall {w q} -> p -! w !⟶ q -> Result p
  refuse : Silent p -> Result p

upR : {a b : U}{p : Proc b}(φ : Tran a b) -> Result p -> Result (φ /| p)
upR φ (speak  s) = speak  (tx-/| s)
upR φ (refuse s) = refuse (silent-/| s)

Oracle : Set
Oracle = Nat -> LR

prophecy : Oracle -> LR
prophecy ol = ol zero

nextOracle : Oracle -> Oracle
nextOracle ol = ol ∘ suc

anyOracle : Oracle
anyOracle _ = left

infixr 50 _::_

_::_ : LR -> Oracle -> Oracle
(l :: or) zero    = l
(l :: or) (suc n) = or n

step : {a : U}{p : Proc a} -> Guard p -> Oracle -> Result p
step og           _  = refuse silent-o
step (>g _)       _  = refuse silent->
step (w !g p)     _  = speak tx-!
step (w ! p +g f) _  = speak tx-+
step (defg x g)   ol with step g ol
... | refuse s₁ = refuse (silent-def s₁)
... | speak  s₁ = speak (tx-def s₁)
step (g₁ ||g g₂)  ol with step g₁ (nextOracle ol)
                        | step g₂ (nextOracle ol)
                        | prophecy ol
... | refuse s₁ | refuse s₂ | _     = refuse (silent-|| s₁ s₂)
... | speak s₁  | refuse s₂ | _     = speak (tx-!| s₁ (sound g₂))
... | refuse s₁ | speak s₂  | _     = speak (tx-|! (sound g₁) s₂)
... | speak s₁  | speak _   | left  = speak (tx-!| s₁ (sound g₂))
... | speak _   | speak s₂  | right = speak (tx-|! (sound g₁) s₂)
step (φ /|g g)    ol = upR φ (step g ol)
