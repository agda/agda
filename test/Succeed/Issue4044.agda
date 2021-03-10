{-# OPTIONS --show-implicit #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit

postulate
  A B C D : Set
  F : (A → A) → (A → A → A) → A
  a : A

data Tree : Set where
  leaf : Tree
  node : (f : (x : A) → Tree) → Tree

tree1 : Nat → Tree
tree1 zero = leaf
tree1 (suc n) = node (λ x → tree1 n)

tree2 : Nat → Tree
tree2 zero = leaf
tree2 (suc n) = node (λ x → tree2 n)

-- In Agda 2.6.0.1, this takes >50 sec and >5GB to typecheck.
test : tree1 5000 ≡ tree2 5000
test = refl
