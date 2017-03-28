module Golden.InsertionSort where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Bool

insert : Nat -> List Nat -> List Nat
insert a [] = a ∷ []
insert x (a ∷ b) with x < a
... | true = x ∷ a ∷ b
... | false = a ∷ (insert x b)

foldr : ∀ {a b : Set} → (a → b → b) → b → List a -> b
foldr f ini [] = ini
foldr f ini (x ∷ l) = f x (foldr f ini l)

insertSort : List Nat -> List Nat
insertSort = foldr insert []

atDef : ∀ {a : Set} → a → List a -> Nat -> a
atDef def (x ∷ l) zero = x
atDef def (x ∷ l) (suc ix) = atDef def l ix
atDef def _ _ = def

lst : List Nat
lst = 4 ∷ 2 ∷ 7 ∷ []

slst : List Nat
slst = insertSort lst

l0 : Nat
l0 = atDef 0 slst 0

l1 : Nat
l1 = atDef 0 slst 1

l2 : Nat
l2 = atDef 0 slst 2
