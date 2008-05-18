
module Dual where

open import Prelude using (flip)
open import Logic.Equivalence
open import Category

_op : Cat -> Cat
ℂ@(cat _ _ _ _ _ _ _ _ _) op = cat Obj
	   (\A B -> B ─→ A)
	    id
	   (\{_}{_}{_} -> flip _∘_)
	   (\{_}{_} -> Eq)
	   (\{_}{_}{_}{_}{_}{_}{_} -> flip cong)
	   (\{_}{_}{_} -> idR)
	   (\{_}{_}{_} -> idL)
	   (\{_}{_}{_}{_}{_}{_}{_} -> sym assoc)
  where open module C = Cat ℂ

{-
open Poly-Cat

dualObj : {ℂ : Cat} -> Obj ℂ -> Obj (ℂ op)
dualObj {cat _ _ _ _ _ _ _ _ _}(obj A) = obj A

undualObj : {ℂ : Cat} -> Obj (ℂ op) -> Obj ℂ
undualObj {cat _ _ _ _ _ _ _ _ _}(obj A) = obj A

dualdualArr : {ℂ : Cat}{A B : Obj ℂ} -> A ─→ B -> dualObj B ─→ dualObj A
dualdualArr {cat _ _ _ _ _ _ _ _ _}{A = obj _}{B = obj _}(arr f) = arr f

dualundualArr : {ℂ : Cat}{A : Obj ℂ}{B : Obj (ℂ op)} ->
		A ─→ undualObj B -> B ─→ dualObj A
dualundualArr {cat _ _ _ _ _ _ _ _ _}{A = obj _}{B = obj _}(arr f) = arr f
-}
