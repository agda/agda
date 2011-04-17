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

-- the following is ok, since Fin _ is really just Nat
toNat : Fin zero -> Nat
toNat (zero _)  = zero
toNat (suc _ i) = suc (toNat i)

data Pos : Nat -> Set where
  pos : (n : Nat) -> Pos (suc n)

f : (n : Nat) -> Fin n -> Pos n
f .(suc n) (zero n)  = pos n
f .(suc n) (suc n i) = pos n
-- cannot infer value of dot pattern

{-
f : (n : Nat) -> Fin n -> Pos n
f .(suc _) (zero _)  = pos _
f .(suc _) (suc _ _) = pos _

f' : (n : Nat) -> Fin n -> Pos n
f' _ (zero _)  = pos _
f' _ (suc _ _) = pos _
-}


