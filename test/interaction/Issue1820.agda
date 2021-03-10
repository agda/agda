data Nat : Set where
  zero : Nat
  suc : (n : Nat) → Nat

test₁ : (n : Nat) → Nat
test₁ n with zero
... | x = {!x!}

data Tree : Set where
  leaf : Tree
  node : Tree → Tree → Tree

test₂ : (n : Tree) → Tree
test₂ n₁ with leaf
... | n = {!n!}
