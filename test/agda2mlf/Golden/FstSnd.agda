module Golden.FstSnd where

open import Agda.Builtin.Nat

data Tuple a b : Set where
  Tup : a -> b -> Tuple a b

fst : {a b : Set} -> Tuple a b -> a
fst (Tup x x₁) = x
snd : {a b : Set} -> Tuple a b -> b
snd (Tup x b) = b


tup1 : Tuple Nat Nat
tup1 = Tup 0 1

a = fst tup1
b = snd tup1
