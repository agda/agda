module PatternSynonymOverloaded where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

pattern ss x = suc (suc x)
pattern ss x = suc x