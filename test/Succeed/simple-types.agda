data Nat : Set
  = Z
  | S Nat

{-# BUILTIN NATURAL Nat #-}

plus : Nat → Nat → Nat
plus Z     n = n
plus (S m) n = S (plus m n)

open import Agda.Primitive

infixr 3 _,_
data _×_ {a} {b} (A : Set a) (B : Set b)
  : Set (a ⊔ b)
  = _,_ A B

swap : {A B : Set} → A × B → B × A
swap (A , B) = B , A

data FTree {a : Level} (A : Set a) : Set a
  = FLeaf A
  | FNode (FTree (A × A))

ftree : FTree Nat
ftree = FNode (FNode (FLeaf ((0 , 1) , 2 , 3)))

open import Agda.Builtin.List

data Tree {l n} (L : Set l) (N : Set n) : Set (l ⊔ n)
  = Leaf L
  | Node N (List (Tree L N))
