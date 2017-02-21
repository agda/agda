module _ where

open import SimpleIO

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

show : Nat -> String
show zero = "."
show (succ n) = "." & (show n)

add : Nat -> Nat -> Nat
add zero m = m
add (succ n) m = add n (succ m)

mult : Nat -> Nat -> Nat
mult zero m = zero
mult (succ n) m = add m (mult n m)

-- NB: Any top-level expression is evaluated.
one two three four : Nat
one = succ zero
two = succ one
three = succ two
four = succ three
seven = add three four
twentyone = mult seven three

showNat : Nat -> IO Unit
showNat n = putStrLn (show n)

e0 e1 : IO Unit
e0 = showNat seven

e1 = showNat twentyone
