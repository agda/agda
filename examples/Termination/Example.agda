
module Example where

loop : Set
loop = loop

_∞_ : Set -> Set -> Set
x ∞ y = x ∞ y

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

bad2 : Nat -> Nat
bad2 (succ x) = bad2 x + bad2 (succ x)
bad2 x        = bad2 x

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


mutual

  badf : Nat ×  Nat -> Nat
  badf (zero , y) = zero
  badf (succ x , zero) = zero
  badf (succ x , succ y) = badg (x , succ y) + badf  (succ (succ x) , y)

  badg : Nat × Nat -> Nat
  badg (zero , y) = zero
  badg (succ x , zero) = zero
  badg (succ x , succ y) = badf (succ x , succ y) +  badg (x , succ (succ y))


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

-- these are ok, however

bla : Nat
bla = succ (succ zero)

mutual

  f'' : Nat -> Nat -> Nat
  f'' zero y = zero
  f'' (succ x) zero = zero
  f'' (succ x) (succ y) = (g'' x (succ y)) + (f'' bla y)

  g'' : Nat -> Nat -> Nat
  g'' zero y = zero
  g'' (succ x) zero = zero
  g'' (succ x) (succ y) = (f'' (succ x) (succ y)) + (g'' x (succ y))


-- Ackermann

ack : Nat -> Nat -> Nat
ack zero y = succ y
ack (succ x) zero = ack x (succ zero)
ack (succ x) (succ y) = ack x (ack (succ x) y)

ack' : Nat × Nat -> Nat
ack' (zero , y) = succ y
ack' (succ x , zero) = ack' (x , succ zero)
ack' (succ x , succ y) = ack' (x , ack' (succ x , y))

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

-- Higher-order example which should not pass the termination checker.
-- (Not the current one, anyway.)

foo : Ord -> (Nat -> Ord) -> Ord
foo ozero    g = ozero
foo (olim f) g = olim (\n -> foo (g n) f)

-- Examples checking that a function can be used with several
-- different numbers of arguments on the right-hand side.

const : {a b : Set1} -> a -> b -> a
const x _ = x

ok : Nat -> Nat -> Set
ok zero     y = Nat
ok (succ x) y = const Nat (const (ok x y) (ok x))

notOK : Set -> Set
notOK x = const (notOK Ord) notOK

-- An example which should fail (37 is an arbitrary number):

data ⊤ : Set where
  tt : ⊤

mutual

  foo37 : ⊤ -> ⊤
  foo37 x = bar37 x

  bar37 : ⊤ -> ⊤
  bar37 tt = foo37 tt

-- Some examples involving with.

-- Not OK:

withNo : Nat -> Nat
withNo n with n
withNo n | m = withNo m

-- OK:

withYes : Nat -> Nat
withYes n with n
withYes n | zero   = zero
withYes n | succ m = withYes m

-- Some rather convoluted examples.

-- OK:

number : Nat
number = zero
  where
  data Foo12 : Nat -> Set where
    foo12 : Foo12 number

-- Should the occurrence of number' in the type signature of foo12
-- really be highlighted here?

number' : Nat
number' with zero
number' | x = g12 foo12
  where
  data Foo12 : Nat -> Set where
    foo12 : Foo12 number'
  abstract
    g12 : {i : Nat} -> Foo12 i -> Nat
    g12 foo12 = zero

-- Tests highlighting (but does not type check yet):

-- number'' : Nat
-- number'' with zero
-- number'' | x = g12 (foo12 x)
--   where
--   data Foo12 : Nat -> Set where
--     foo12 : (n : Nat) -> Foo12 (number'' | n)
--   abstract
--     g12 : {i : Nat} -> Foo12 i -> Nat
--     g12 (foo12 n) = n


data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

infixr 50 _::_

-- butlast function
good1 : {A : Set} -> List A -> A 
good1 (a :: []) = a
good1 (a :: b :: bs) = good1 (b :: bs)

infixl 10 _⊕_
postulate
  _⊕_ : {A : Set} -> A -> A -> A  -- non-deterministic choice


-- a funny formulation of insert
-- insert (a :: l)  inserts a into l 
insert : {A : Set} -> List A -> List A
insert [] = []
insert (a :: []) = a :: []
insert (a :: b :: bs) = a :: b :: bs ⊕        -- case a <= b 
                        b :: insert (a :: bs) -- case a > b

-- list flattening
flat : {A : Set} -> List (List A) -> List A
flat [] = []
flat ([] :: ll) = flat ll
flat ((x :: l) :: ll) = x :: flat (l :: ll)


-- leaf-labelled trees

data Tree (A : Set) : Set where
  leaf : A -> Tree A
  node : Tree A -> Tree A -> Tree A

-- flattening (does not termination check)

tflat : {A : Set} -> Tree A -> List A
tflat (leaf a) = a :: []
tflat (node (leaf a) r) = a :: tflat r
tflat (node (node l1 l2) r) = tflat (node l1 (node l2 r))


-- Maximum of 3 numbers
-- mixing tupling and swapping: does not work with structured orders

max3' : Nat × Nat -> Nat -> Nat
max3' (zero , zero) z = z
max3' (zero , y) zero = y
max3' (x , zero) zero = x
max3' (succ x , succ y) zero   = succ (max3' (x , y) zero)
max3' (succ x , zero) (succ z) = succ (max3' (x , z) zero)
max3' (zero , succ y) (succ z) = succ (max3' (y , z) zero)
max3' (succ x , succ y) (succ z) = succ (max3' (z , x) y)
