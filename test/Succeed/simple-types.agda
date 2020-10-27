data Nat : Set
  = Z
  | S Nat

{-# BUILTIN NATURAL Nat #-}

plus : Nat → Nat → Nat
plus Z     n = n
plus (S m) n = S (plus m n)

open import Agda.Primitive

data Pair {a} {b} (A : Set a) (B : Set b)
  : Set (a ⊔ b)
  = MkPair A B

swap : {A B : Set} → Pair A B → Pair B A
swap (MkPair A B) = MkPair B A

data FTree {a : Level} (A : Set a) : Set a
  = FLeaf A
  | FNode (FTree (Pair A A))

ftree : FTree Nat
ftree = FNode (FNode (FLeaf (MkPair (MkPair 0 1) (MkPair 2 3))))

open import Agda.Builtin.List

data Tree {l n} (L : Set l) (N : Set n) : Set (l ⊔ n)
  = Leaf L
  | Node N (List (Tree L N))
