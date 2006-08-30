
module IllTyped where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Bool : Set where
  false : Bool
  true  : Bool

F : Nat -> Set
F  zero	  = Nat
F (suc x) = Bool

postulate
  D : (x:Nat)(y:F x) -> Set
  T : Nat -> Set

  f : {x:Nat -> Nat}{y:F (x zero)} ->
      (T (x zero) -> T (suc zero)) ->
      (D zero zero -> D (x zero) y) ->
      Nat

test = f {?} (\x -> x) (\x -> x)


