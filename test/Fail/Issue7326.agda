
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Reflection

macro
  magic : Term → TC ⊤
  magic hole = unify hole (pat-lam [] [])

data ⊥ : Set where

bad : ⊥ → ⊤
bad = magic   -- __IMPOSSIBLE__ at Unquote.hs:513
