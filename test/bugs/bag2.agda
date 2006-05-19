module Top where

module Prelude where

  data Bool : Set where
    True  : Bool
    False : Bool

  data Pair (a, b : Set) : Set where
    pair : a -> b -> Pair a b

  fst : {a, b : Set} -> Pair a b -> a
  fst {a} {b} (pair x y) = x

  snd : {a, b : Set} -> Pair a b -> b
  snd {a} {b} (pair x y) = y

  data Either (a, b : Set) : Set where
    left  : a -> Either a b
    right : b -> Either a b

  data Absurd : Set where

  data Not (a : Set) : Set where
    not : (a -> Absurd) -> Not a

  -- Not : Set -> Set
  -- Not a = a -> Absurd

module Equiv where

  open Prelude

  data Equiv (a : Set) : Set1 where
    equiv :  ((==) : a -> a -> Set)
          -> (refl  : (x : a) -> x == x)
          -> (sym   : (x, y : a) -> x == y -> y == x)
          -> (trans : (x, y, z : a) -> x == y -> y == z -> x == z)
          -> Equiv a

  rel : {a : Set} -> Equiv a -> (a -> a -> Set)
  rel {a} (equiv (==) _ _ _) = (==)

  data Decidable {a : Set} ((==) : a -> a -> Set) : Set where
    dec : ((x, y : a) -> Either (x == y) (Not (x == y))) -> Decidable (==)

  data DecidableEquiv (a : Set) : Set1 where
    decEquiv : (eq : Equiv a) -> Decidable (rel eq) -> DecidableEquiv a

  rel' :  {a : Set} -> (eq : DecidableEquiv a) -> (a -> a -> Set)
  rel' {a} (decEquiv eq _) = rel eq

  decRel :  {a : Set} -> (eq : DecidableEquiv a) -> (x, y : a)
         -> Either (rel' eq x y) (Not (rel' eq x y))
  decRel {a} (decEquiv _ dec) x y = dec x y
