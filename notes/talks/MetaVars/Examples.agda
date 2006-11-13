
module Examples where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Bool : Set where
  true  : Bool
  false : Bool

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y

not : Bool -> Bool
not x = if x then false else true

isZero : Nat -> Bool
isZero zero    = true
isZero (suc _) = false

F : Bool -> Set
F true  = Nat
F false = Bool

f : (x : Bool) -> F x -> F (not x)
f true n  = isZero n
f false b = if b then zero else suc zero

test : Bool
test = f ? zero

