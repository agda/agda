-- examples for termination with tupled arguments

module Tuple where

data Nat : Set where
   zero : Nat
   succ : Nat -> Nat

data Pair (A : Set) (B : Set) : Set where
  pair : A -> B -> Pair A B

-- uncurried addition
add : Pair Nat Nat -> Nat
add (pair x (succ y)) = succ (add (pair x y))
add (pair x zero)     = x


data T (A : Set) (B : Set) : Set where
  c1 : A -> B -> T A B
  c2 : A -> B -> T A B

{-
-- constructor names do not matter
add' : T Nat Nat -> Nat
add' (c1 x (succ y)) = succ (add' (c2 x y))
add' (c2 x (succ y)) = succ (add' (c1 x y))
add' (c1 x zero) = x
add' (c2 x zero) = x

-- additionally: permutation of arguments
add'' : T Nat Nat -> Nat
add'' (c1 x (succ y)) = succ (add'' (c2 y x))
add'' (c2 (succ y) x) = succ (add'' (c1 x y))
add'' (c1 x zero) = x
add'' (c2 zero x) = x
-}
