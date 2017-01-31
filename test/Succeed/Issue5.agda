-- Andreas, 2017-01-18, issue #5 is fixed
-- reported by Ulf 2007-10-24

data Nat : Set where
  zero : Nat

data Vec : Nat -> Set where
  []   : Vec zero

f : (n : Nat) -> Vec n -> Nat
f n@._ [] = n
