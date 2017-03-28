module Golden.Index where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Bool

lst : List Nat
lst = 1 ∷ 2 ∷ []

atDef : ∀ {a : Set} → a → List a -> Nat -> a
atDef def (x ∷ l) zero = x
atDef def (x ∷ l) (suc ix) = atDef def l ix
atDef def _ _ = def

l0 : Nat
l0 = atDef 0 lst 0

l1 : Nat
l1 = atDef 0 lst 1

l2 : Nat
l2 = atDef 0 lst 2
