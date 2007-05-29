module Example where

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

id : Nat -> Nat
id zero = zero
id (succ n) = succ (id n)

bad : Nat -> Nat
bad n = bad n

_+_ : Nat -> Nat -> Nat
zero     + n = n
(succ m) + n = succ (m + n)

data Bool : Set where
    true : Bool
    false : Bool

_&&_ : Bool -> Bool -> Bool
true && a = a
false && a = false

mutual
  
  even : Nat -> Bool
  even zero = true
  even (succ n) = odd n

  odd  : Nat -> Bool
  odd zero = false
  odd (succ n) = even n 

data Ty : {_ : Nat} -> Set where
    Base : forall {n} -> Ty {succ n}
    Arr  : forall {n} -> Ty {n} -> Ty {n} -> Ty {succ n}

eqty : forall {n} -> Ty {n} -> Ty {n} -> Bool
eqty Base Base = true
eqty (Arr a b) (Arr a' b') = (eqty a a') && (eqty b b')
eqty _ _ = false

subty : forall {n} -> Ty {n} -> Ty {n} -> Bool
subty Base Base = true
subty (Arr a b) (Arr a' b') = (subty a' a) && (subty b b')
subty _ _ = false

subty' : forall {n} -> Ty {n} -> Ty {n} -> Bool
subty' Base Base = true
subty' {succ n} (Arr {.n} a b) (Arr .{n} a' b') 
     = (subty' {n} a' a) && (subty' {n} b b')
subty' _ _ = false

 