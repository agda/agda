module Nat where

data Nat : Set

data Nat where
  zero : Nat
  suc  : Nat -> Nat

plus : Nat -> Nat -> Nat
plus zero    n = n
plus (suc m) n = suc (plus m n)

elim : (P : (n : Nat) -> Set) ->
       (z : P (plus zero zero)) ->
       (s : (n : Nat) -> P (plus zero n) -> P (plus (suc zero) n)) ->
       (n : Nat) -> P n
elim P z s zero    = z
elim P z s (suc n) = s n (elim P z s n)
