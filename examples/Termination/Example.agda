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

-- the following is enough for making it termination check
subty' : forall {n} -> Ty {n} -> Ty {n} -> Bool
subty' Base Base = true
subty' {succ n} (Arr a b) (Arr a' b') 
     = (subty' a' a) && (subty' b b')
subty' _ _ = false

subty'' : forall {n} -> Ty {n} -> Ty {n} -> Bool
subty'' Base Base = true
subty'' {succ n} (Arr {.n} a b) (Arr .{n} a'' b'') 
     = (subty'' {n} a'' a) && (subty'' {n} b b'')
subty'' _ _ = false

 
data _×_ (A B : Set) : Set where
    _,_ : A -> B -> A × B

add : Nat × Nat -> Nat
add (zero   , m) = m
add (succ n , m) = succ (add (n , m))

eq : Nat × Nat -> Bool
eq (zero   , zero  ) = true
eq (succ n , succ m) = eq (n , m)
eq _ = false


-- the following should not termination check

mutual 

  f : Nat -> Nat -> Nat

  f zero y = zero
  f (succ x) zero = zero
  f (succ x) (succ y) = (g x (succ y)) + (f  (succ (succ x)) y) 

  g : Nat -> Nat -> Nat
 
  g zero y = zero
  g (succ x) zero = zero
  g (succ x) (succ y) = (f (succ x) (succ y)) + (g x (succ (succ y)))


-- these are ok, however

mutual 

  f' : Nat -> Nat -> Nat

  f' zero y = zero
  f' (succ x) zero = zero
  f' (succ x) (succ y) = (g' x (succ y)) + (f'  (succ (succ x)) y) 

  g' : Nat -> Nat -> Nat
 
  g' zero y = zero
  g' (succ x) zero = zero
  g' (succ x) (succ y) = (f' (succ x) (succ y)) + (g' x (succ y))


-- Ackermann

ack : Nat -> Nat -> Nat
ack zero y = succ y
ack (succ x) zero = ack x (succ zero)
ack (succ x) (succ y) = ack x (ack (succ x) y)

-- Maximum of 3 numbers

max3 : Nat -> Nat -> Nat -> Nat
max3 zero zero z = z
max3 zero y zero = y
max3 x zero zero = x
max3 (succ x) (succ y) zero = succ (max3 x y zero)
max3 (succ x) zero (succ z) = succ (max3 x zero z)
max3 zero (succ y) (succ z) = succ (max3 zero y z)
max3 (succ x) (succ y) (succ z) = succ (max3 x y z)

-- addition of Ordinals

data Ord : Set where
   ozero : Ord
   olim  : (Nat -> Ord) -> Ord

addord : Ord -> Ord -> Ord
addord x ozero = x
addord x (olim f) = olim (\ n -> addord x (f n))

