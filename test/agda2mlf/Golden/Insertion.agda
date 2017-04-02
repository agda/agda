module Golden.Insertion where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Bool

insert : Nat -> List Nat -> List Nat
insert a [] = a ∷ []
insert x (a ∷ b) with x < a
... | true = x ∷ a ∷ b
... | false = a ∷ (insert x b)

lst : List Nat
lst = 2 ∷ []

slst : List Nat
slst = insert 3 lst

atDef : ∀ {a : Set} → a → List a -> Nat -> a
atDef def (x ∷ l) zero = x
atDef def (x ∷ l) (suc ix) = atDef def l ix
atDef def _ _ = def

l0 : Nat
l0 = atDef 0 slst 0

l1 : Nat
l1 = atDef 0 slst 1
