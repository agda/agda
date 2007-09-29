
open import Proc

module Interp (param : Param) where

open import Basics
private open module P = Process param

open Tran

hear : {a : U}{p : Proc a} -> Guard p -> LT a -> Proc a
hear {p = p} g    ⊥        = p
hear og           (lift v) = o
hear (w !g p)     (lift v) = w ! p
hear (>g f)       (lift v) = f v
hear (_ ! _ +g f) (lift v) = f v
hear (g₁ ||g g₂)  (lift v) = hear g₁ (lift v) || hear g₂ (lift v)
hear (φ /|g g)    (lift v) = φ /| hear g (downV φ v)
hear (defg x g)   (lift v) = hear g (lift v)

data Result (a : U) : Set where
  _/_    : LT a -> Proc a -> Result a
  refuse : Result a

upR : {a b : U} -> Tran a b -> Result b -> Result a
upR φ (w / p) = (upV φ =<< w) / φ /| p
upR φ refuse  = refuse

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

step : {a : U}{p : Proc a} -> Guard p -> Oracle -> Result a
step og           _  = refuse
step (>g _)       _  = refuse
step (w !g p)     _  = w / p
step (w ! p +g f) _  = w / p
step (defg x g)   ol = step g ol
step (g₁ ||g g₂)  ol with step g₁ (nextOracle ol)
                        | step g₂ (nextOracle ol)
                        | prophecy ol
... | refuse | refuse | _     = refuse
... | w / p  | refuse | _     = w / (p || hear g₂ w)
... | refuse | w / p  | _     = w / (hear g₁ w || p)
... | w / p  | _ / _  | left  = w / (p || hear g₂ w)
... | _ / _  | w / p  | right = w / (hear g₁ w || p)
step (φ /|g g)    ol = upR φ (step g ol)
