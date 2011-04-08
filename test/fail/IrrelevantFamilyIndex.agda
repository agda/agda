-- Andreas, 2011-04-07

module IrrelevantFamilyIndex where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- irrelevant index
data Fin : .Nat -> Set where
  zero : .(n : Nat) -> Fin (suc n)
  suc  : .(n : Nat) -> Fin n -> Fin (suc n)

t : Fin zero
t = zero zero

data Pos : Nat -> Set where
  pos : (n : Nat) -> Pos (suc n)

f : (n : Nat) -> Fin n -> Pos n
f .(suc n) (zero n)  = pos n
f .(suc n) (suc n i) = pos n
-- this does not check,  as expected

{-
f : (n : Nat) -> Fin n -> Pos n
f .(suc _) (zero _)  = pos _
f .(suc _) (suc _ _) = pos _
-}

