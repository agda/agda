
module Problem1 where

-- 1.1

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- 1.2

infixl 60 _+_

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

-- 1.3

infixl 70 _*_

_*_ : Nat -> Nat -> Nat
zero  * m = zero
suc n * m = m + n * m

-- 1.4

infix 30 _==_

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

cong : {A B : Set}(f : A -> B){x y : A} -> x == y -> f x == f y
cong f refl = refl

assoc : (x y z : Nat) -> x + (y + z) == (x + y) + z
assoc zero    y z = refl
assoc (suc x) y z = cong suc (assoc x y z)

-- Alternative solution using 'with'. Note that in order
-- to be able to pattern match on the induction hypothesis
-- we have to abstract (using with) over the left hand side
-- of the equation.

assoc' : (x y z : Nat) -> x + (y + z) == (x + y) + z
assoc' zero    y z = refl
assoc' (suc x) y z with x + (y + z) | assoc x y z
...                | .((x + y) + z) | refl = refl
