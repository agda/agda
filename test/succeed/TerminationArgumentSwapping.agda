module TerminationArgumentSwapping where

-- subtyping simple types

data Bool : Set where
   true  : Bool
   false : Bool

_&&_ : Bool -> Bool -> Bool
true && a = a
false && a = false

data Ty : Set where
   bot : Ty
   top : Ty
   arr : Ty -> Ty -> Ty

subty : Ty -> Ty -> Bool
subty bot _ = true
subty _ top = true
subty (arr a b) (arr a' b') = subty a' a && subty b b'
subty _ _ = false


-- maximum with happy swapping

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

-- Maximum of 3 numbers

max3 : Nat -> Nat -> Nat -> Nat
max3 zero zero z = z
max3 zero y zero = y
max3 x zero zero = x
max3 (succ x) (succ y) zero = succ (max3 x y zero)
max3 (succ x) zero (succ z) = succ (max3 x z zero)
max3 zero (succ y) (succ z) = succ (max3 y z zero)
max3 (succ x) (succ y) (succ z) = succ (max3 z x y)

-- can also be done with sized types
-- max3 : Nat^i -> Nat^i -> Nat^i -> Nat^i

-- swapping with higher-order datatypes

data Ord : Set where
   ozero : Ord
   olim  : (Nat -> Ord) -> Ord

foo : Ord -> (Nat -> Ord) -> Ord
foo ozero    g = ozero
foo (olim f) g = olim (\n -> foo (g n) f)
